-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.reveal_prior_two_sided_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:45:05.551203+00:00
-- url     : https://prove2.me/submissions/c24df50f-8dd6-4f6f-905c-198ae5804903

import Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_prior_one_sided_bernstein
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution {A : Type} [Fintype A] (n : ℕ) (s η : ℝ) (ν z : A → ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hν : ∀ a, 0 ≤ ν a) (hνsum : (∑ a, ν a) = 1)
    (hz : ∀ a, |z a| ≤ 1) (hcenter : (∑ a, ν a * z a) = 0) :
    (∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
      (∏ v, ν (y v)) * (if s*η*n/2 ≤ |∑ v, z (y v)| then 1 else 0)) ≤
        2*Real.exp (-(s*η^2/12)*n) := by
  classical
  let a := s*η*n/2
  have hpoint (U : Finset (Fin n)) (y : {v : Fin n // v ∈ U} → A) :
      (if a ≤ |∑ v, z (y v)| then (1:ℝ) else 0) ≤
        (if a ≤ ∑ v, z (y v) then 1 else 0) + (if a ≤ -(∑ v, z (y v)) then 1 else 0) := by
    by_cases hx : 0 ≤ ∑ v, z (y v)
    · rw [abs_of_nonneg hx]
      split_ifs <;> norm_num
    · rw [abs_of_neg (lt_of_not_ge hx)]
      split_ifs <;> norm_num
  have hbound : (∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
      (∏ v, ν (y v)) * (if a ≤ |∑ v, z (y v)| then 1 else 0)) ≤
      (∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
      (∏ v, ν (y v)) * (if a ≤ ∑ v, z (y v) then 1 else 0)) +
      (∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
      (∏ v, ν (y v)) * (if a ≤ -(∑ v, z (y v)) then 1 else 0)) := by
    have hh : (∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
        (∏ v, ν (y v)) * (if a ≤ |∑ v, z (y v)| then 1 else 0)) ≤
        ∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
        (∏ v, ν (y v)) * ((if a ≤ ∑ v, z (y v) then 1 else 0) +
          (if a ≤ -(∑ v, z (y v)) then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro U hU
      apply mul_le_mul_of_nonneg_left _
      · unfold revealProb
        exact mul_nonneg (pow_nonneg hs _) (pow_nonneg (sub_nonneg.mpr hs1) _)
      · apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_left (hpoint U y) (Finset.prod_nonneg fun v hv => hν (y v))
    simpa only [mul_add,Finset.sum_add_distrib] using hh
  have hplus := reveal_prior_one_sided_bernstein n s η ν z hs hs1 hη hη1 hν hνsum hz hcenter
  have hminus := reveal_prior_one_sided_bernstein n s η ν (fun x => -z x) hs hs1 hη hη1 hν hνsum
    (by simpa using hz) (by simp only [mul_neg,Finset.sum_neg_distrib,hcenter,neg_zero])
  have hminus' : (∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
      (∏ v, ν (y v)) * (if a ≤ -(∑ v, z (y v)) then 1 else 0)) ≤
      Real.exp (-(s*η^2/12)*n) := by
    simpa only [Finset.sum_neg_distrib] using hminus
  exact hbound.trans (by linarith)
