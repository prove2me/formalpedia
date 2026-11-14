-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.reveal_two_sided_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:38:50.754199+00:00
-- url     : https://prove2.me/submissions/045335f3-100d-4307-bb4a-3f0f454048b7

import Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_one_sided_bernstein
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (n : ℕ) (s η : ℝ) (z : Fin n → ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hz : ∀ v, |z v| ≤ 1) :
    (∑ U : Finset (Fin n), revealProb s U *
      (if s*η*n/2 ≤ |(∑ v ∈ U, z v) - s*(∑ v : Fin n, z v)| then 1 else 0)) ≤
        2*Real.exp (-(s*η^2/12)*n) := by
  classical
  let a := s*η*n/2
  let X := fun U : Finset (Fin n) => (∑ v ∈ U, z v) - s*(∑ v : Fin n, z v)
  have hprob (U : Finset (Fin n)) : 0 ≤ revealProb s U := by
    unfold revealProb
    exact mul_nonneg (pow_nonneg hs _) (pow_nonneg (sub_nonneg.mpr hs1) _)
  have hpnt (U : Finset (Fin n)) :
      (if a ≤ |X U| then (1:ℝ) else 0) ≤
        (if a ≤ X U then 1 else 0) + (if a ≤ -X U then 1 else 0) := by
    by_cases hx : 0 ≤ X U
    · rw [abs_of_nonneg hx]
      split_ifs <;> norm_num
    · rw [abs_of_neg (lt_of_not_ge hx)]
      split_ifs <;> norm_num
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Finset (Fin n))))
    (fun U _ => mul_le_mul_of_nonneg_left (hpnt U) (hprob U))
  simp only [mul_add,Finset.sum_add_distrib] at hsum
  have hplus := reveal_one_sided_bernstein n s η z hs hs1 hη hη1 hz
  have hminus := reveal_one_sided_bernstein n s η (fun v => -z v) hs hs1 hη hη1 (by simpa using hz)
  have hminus' : (∑ U : Finset (Fin n), revealProb s U * (if a ≤ -X U then 1 else 0)) ≤
      Real.exp (-(s*η^2/12)*n) := by
    convert hminus using 1
    apply Finset.sum_congr rfl
    intro U hU
    simp only [Finset.sum_neg_distrib]
    dsimp [a,X]
    congr 2
    ring
  exact hsum.trans (by linarith)
