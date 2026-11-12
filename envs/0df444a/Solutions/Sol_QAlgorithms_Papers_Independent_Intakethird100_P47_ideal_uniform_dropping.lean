-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P47.ideal_uniform_dropping
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:25:23.709864+00:00
-- url     : https://prove2.me/submissions/b6527a3c-f961-4725-8cf8-4feb553e39c7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

open scoped ComplexConjugate

open scoped BigOperators

open QAlgorithms.Papers.Independent.Intakethird100.P47 in
theorem solution (p : Behavior) (hp : IsBehavior p)
    (h00 : p false false false false = (5 * Real.sqrt 5 - 11) / 2)
    (h11 : p true true false false = Real.sqrt 5 - 2)
    (h10 : p true false false false = 0) (h01 : p false true false false = 0) :
    let x := (5 * Real.sqrt 5 - 11) / 2
    let y := Real.sqrt 5 - 2
    let w := binarySettingLaw (1 / 2) (1 / 2)
    let j := acceptedLaw p w
    let k : Bool → ℝ := fun A => if A then x / y else 1
    0 < siftingProbability p w ∧ 0 < x / y ∧ x / y ≤ 1 ∧
    siftingProbability p w = (x + y) / 4 ∧
    retention j k = 2 * x / (x + y) ∧
    siftingProbability p w * retention j k = (5 * Real.sqrt 5 - 11) / 4 ∧
    (∀ A, aliceMarginal (retainedLaw j k) A = 1 / 2) ∧
    (∑ A, retainedLaw j k A A) = 1 ∧
    max (aliceMarginal (retainedLaw j k) false)
      (aliceMarginal (retainedLaw j k) true) = 1 / 2 := by
  intro x y w j k
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hxv : x = (5 * Real.sqrt 5 - 11) / 2 := rfl
  have hyv : y = Real.sqrt 5 - 2 := rfl
  have hx : 0 < x := by rw [hxv]; nlinarith
  have hy : 0 < y := by rw [hyv]; nlinarith
  have hxy : x ≤ y := by rw [hxv, hyv]; nlinarith
  have hxy0 : x + y ≠ 0 := by linarith
  have hy0 : y ≠ 0 := hy.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hxd : p false false false false = x := h00
  have hyd : p true true false false = y := h11
  have hkt : k true = x / y := rfl
  have hkf : k false = 1 := rfl
  have hw : ∀ A B, w A B = 1 / 4 := by
    intro A B
    cases A <;> cases B <;> norm_num [w, binarySettingLaw]
  have hS : siftingProbability p w = (x + y) / 4 := by
    simp only [siftingProbability, acceptedMass, hw, Fintype.sum_bool, hxd, hyd, h10, h01]
    ring
  have hjv : ∀ A B, j A B = p A B false false / (x + y) := by
    intro A B
    simp only [j, acceptedLaw, acceptedMass, hw, hS]
    rw [div_div_eq_mul_div]
    congr 1
    ring
  have hR : retention j k = 2 * x / (x + y) := by
    simp only [retention, hjv, Fintype.sum_bool, hxd, hyd, h10, h01, hkt, hkf]
    field_simp <;> ring
  have hM : ∀ A, aliceMarginal (retainedLaw j k) A = 1 / 2 := by
    intro A
    cases A
    · simp only [aliceMarginal, retainedLaw, hR, hjv, Fintype.sum_bool, hxd, h01, hkf]
      field_simp <;> ring
    · simp only [aliceMarginal, retainedLaw, hR, hjv, Fintype.sum_bool, hyd, h10, hkt]
      field_simp <;> ring
  refine ⟨by rw [hS]; linarith, div_pos hx hy, (div_le_one hy).mpr hxy, hS, hR, ?_, hM, ?_, ?_⟩
  · have e : (x + y) / 4 * (2 * x / (x + y)) = x / 2 := by
      rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero (by norm_num) hxy0) (by norm_num)]
      ring
    rw [hS, hR, e, hxv]
    ring
  · simp only [retainedLaw, hR, hjv, Fintype.sum_bool, hxd, hyd, hkt, hkf]
    field_simp <;> ring
  · rw [hM, hM, max_self]
