module

public import Veir.Data.PBV.Lemmas
public import Veir.Data.PBV.Mask

/-! # Rewriting a parametric expression into a concrete, single-width one.

`eq_iff` introduces a `setWidth o` at the root of the goal, and the remaining
lemmas push it down towards the leaves, masking the result of every
width-sensitive operation. See `Veir.Data.PBV` for more details.
-/

namespace Veir.Data.PBV

public section


/-- Introducing `setWidth o` at the root.
`o` must be the first binder, since it should be bound to the concrete width
being used in the proof..
 -/
theorem eq_iff (o : Nat) {w : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w), (a = b) = (a.setWidth o = b.setWidth o) := by
  intro a b
  apply propext
  exact ⟨fun hab => hab ▸ rfl, fun hab => BitVec.setWidth_inj h hab⟩


/-! ## Pushing `setWidth o` towards the leaves — leaves and width changes -/

theorem setWidth_setWidth {w o : Nat} (h : w ≤ o) :
    ∀ {u : Nat} (a : BitVec u),
      (a.setWidth w).setWidth o = a.setWidth o &&& maskOfWidth o w := by
  intro u a
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_mod_pow_of_le h]

/-! ## Width-sensitive arithmetic: mask the result -/

theorem setWidth_add {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w),
      (a + b).setWidth o = (a.setWidth o + b.setWidth o) &&& maskOfWidth o w := by
  intro a b
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_add, BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h,
    Nat.mod_mod_pow_of_le h, BitVec.toNat_add]

theorem setWidth_mul {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w),
      (a * b).setWidth o = (a.setWidth o * b.setWidth o) &&& maskOfWidth o w := by
  intro a b
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h,
    Nat.mod_mod_pow_of_le h, BitVec.toNat_mul]

theorem self_mod_pow_of_le {x w o : Nat} (h : w ≤ o) :
    x ^ o % x ^ w = 0 := by
  cases h
  · simp
  · grind [Nat.mod_eq_zero_of_dvd, Nat.pow_dvd_pow]

theorem self_lt_of_lt {w o : Nat} {x : BitVec w} (h : w ≤ o) : x.toNat < 2^o := by
  grind [Nat.pow_le_pow_right (n := 2) (by grind) h]

theorem two_pow_sub_mod_of_le {w o n : Nat } (h : w ≤ o) (hn : n ≤ 2 ^ w) :
    (2 ^ o - n) % 2 ^ w = (2 ^ w - n) % 2 ^ w := by
  have h0 : (2 ^ o - 2 ^ w) % 2 ^ w = 0 :=
    Nat.sub_mod_eq_zero_of_mod_eq (by rw [self_mod_pow_of_le h, Nat.mod_self])
  have : (2 ^ o - n) = (2 ^ w - n + 2 ^ o - 2^w) := by grind[Nat.mul_sub_one]
  simp [this, Nat.add_sub_assoc (by apply Nat.pow_le_pow_right (n := 2) (by grind) h), Nat.add_mod, h0]

theorem setWidth_neg {w o : Nat} (h : w ≤ o) (b : BitVec w) :
    (- b).setWidth o = (- b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_neg, BitVec.toNat_neg, Nat.mod_mod_pow_of_le h, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (self_lt_of_lt (x := b) h), two_pow_sub_mod_of_le h (by grind)]

theorem setWidth_sub {w o : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a - b).setWidth o = (a.setWidth o - b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_setWidth_of_le h,
    BitVec.toNat_setWidth_of_le h, Nat.mod_mod_pow_of_le h, Nat.add_mod,
    two_pow_sub_mod_of_le h (Nat.le_of_lt b.isLt), ← Nat.add_mod]

theorem setWidth_shiftLeft {w o : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a <<< b).setWidth o = (a.setWidth o <<< b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp [BitVec.toNat_shiftLeft, Nat.mod_mod_pow_of_le h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (self_lt_of_lt (x := b) h)]

theorem setWidth_shiftLeft' {w o : Nat} (h : w ≤ o) (a : BitVec w) (b : Nat) :
    (a <<< b).setWidth o = (a.setWidth o <<< b) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp [BitVec.toNat_shiftLeft, Nat.mod_mod_pow_of_le h, Nat.shiftLeft_eq]

theorem setWidth_ushiftRight {w o : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a >>> b).setWidth o = (a.setWidth o >>> b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (self_lt_of_lt h), Nat.div_mod_eq_div a.isLt]

theorem setWidth_udiv {w o : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a / b).setWidth o = (a.setWidth o / b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp [BitVec.toNat_udiv, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (self_lt_of_lt h), Nat.div_mod_eq_div a.isLt]

theorem setWidth_umod {w o : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a % b).setWidth o = (a.setWidth o % b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp [BitVec.toNat_umod, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (self_lt_of_lt h), Nat.mod_mod_eq_mod_of_lt_right a.isLt]

/-- Sign extension fills above the source width `v` with the sign bit,
and then masks to the target width. -/
theorem setWidth_signExtend_eq_and_maskOfWidth {t v o : Nat} (hvo : v ≤ o) :
    ∀ (a : BitVec v),
      (a.signExtend t).setWidth o
        = ((a.setWidth o) ||| (cond a.msb (~~~(maskOfWidth o v)) 0#o)) &&& maskOfWidth o t := by
  intro a
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_setWidth, getLsbD_maskOfWidth]
  by_cases hiv : i < v
  · -- Below the source width: the sign fill is masked out.
    have hio : i < o := by lia
    have hmask : (maskOfWidth o v)[i] = true := by
      rw [getElem_maskOfWidth i hio]; simp [hiv]
    cases hmsb : a.msb <;> grind
  · -- At or above the source width: `a` has no bit here, so the result is the sign bit.
    rw [BitVec.getLsbD_of_ge a i (by lia)]
    cases hmsb : a.msb <;>
      simp [hiv, getLsbD_maskOfWidth, Bool.and_comm]

/-- `a ++ b` shifts `a` up by the width of `b`; at the blast width that shift
is a multiplication by `2^w = maskOfWidth o w + 1`, and the two halves no
longer overlap, so they can be recombined with `|||`. -/
theorem setWidth_append_eq_or_mul_maskOfWidth_add_one {w o : Nat} (h : w ≤ o) :
    ∀ {v : Nat} (a : BitVec v) (b : BitVec w), v + w ≤ o →
      (a ++ b).setWidth o
        = ((a.setWidth o) * (maskOfWidth o w + 1#o)) ||| b.setWidth o := by
  intro v a b hvw
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_setWidth_of_le, hvw, h,
      BitVec.toNat_append, maskOfWidth_add_one_eq_twoPow h,
      BitVec.mul_twoPow_eq_shiftLeft, BitVec.toNat_shiftLeft]
  congr 1
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, BitVec.toNat_setWidth_of_le (by lia), Nat.mod_eq_of_lt]
  have a_lt_vw := Nat.mul_lt_mul_of_lt_of_le a.isLt (Nat.le_refl _) (Nat.two_pow_pos w)
  grind [Nat.pow_le_pow_right (n := 2) (by lia) hvw]

/-- `setWidth` of a constant is the constant anded with the mask. -/
theorem setWidth_ofNat {o w n : Nat} (h : w ≤ o) :
    BitVec.setWidth o (BitVec.ofNat w n) = (BitVec.ofNat o n) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp [Nat.mod_mod_pow_of_le h]

/-! ## Width-sensitive bitwise operations: mask the result -/

-- Missing Theorems:
-- not
-- and
-- or
-- xor


/-! ### The sign bit: a test against the mask's top bit -/

/-- `a.msb` can be implemented by masking the sign bit,
which are definitions the bitblaster can see. -/
theorem msb_eq_and_signBitOfMask_maskOfWidth_ne_zero (o : Nat) {w : Nat} (h : w ≤ o) :
    ∀ (a : BitVec w),
      a.msb = (((a.setWidth o) &&& signBitOfMask (maskOfWidth o w)) != 0#o) := by
  intro a
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · -- `BitVec 0` has no bits, so both sides are `false`.
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_of_ge _ _ (by lia)]
    simp
  · rw [signBitOfMask_maskOfWidth_eq_twoPow_of_pos h hw,
      BitVec.and_twoPow, BitVec.getLsbD_setWidth,
      BitVec.msb_eq_getLsbD_last]
    have hlt : w - 1 < o := by lia
    simp only [hlt, decide_true, Bool.true_and]
    cases a.getLsbD (w - 1)
    · simp
    · simp [BitVec.twoPow_ne_zero hlt]
