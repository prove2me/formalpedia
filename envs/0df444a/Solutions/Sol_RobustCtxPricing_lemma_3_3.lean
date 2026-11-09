-- Prove2me | solution 1 for RobustCtxPricing.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T15:34:25.993893+00:00
-- url     : https://prove2.me/submissions/b49ee91f-054b-434b-8533-42d8a379eb9a

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence

open RobustCtxPricing in
theorem solution (d : ℕ) (hd : 1 ≤ d) (ϵ : ℝ) (T : ℕ) (θ : EuclideanSpace ℝ (Fin d))
    (hθ : θ ∈ Theta d) (H : List (EuclideanSpace ℝ (Fin d) × ℝ)) (hH : SetCorrect ϵ θ H)
    (u : EuclideanSpace ℝ (Fin d)) (lam : Fin H.length → ℝ) (hlam : PredictsWith ϵ T H u lam) :
    inner ℝ θ u ∈ Set.Icc (estimate H lam - 1 / (8 * (T : ℝ))) (estimate H lam + 1 / (8 * (T : ℝ))) := by
  have hθ1 : ‖θ‖ ≤ 1 := by
    unfold Theta at hθ; rwa [mem_closedBall_zero_iff] at hθ
  set v := u - ∑ i, lam i • (H.get i).1 with hv
  have hdecomp : inner ℝ θ u - estimate H lam =
      inner ℝ θ v + ∑ i, lam i * (inner ℝ θ (H.get i).1 - (H.get i).2) := by
    rw [hv, inner_sub_right, inner_sum]
    unfold estimate
    simp only [real_inner_smul_right, mul_sub, Finset.sum_sub_distrib]
    ring
  have h1 : |inner ℝ θ v| ≤ ‖v‖ := by
    have := abs_real_inner_le_norm θ v
    nlinarith [norm_nonneg v, norm_nonneg θ]
  have h2 : |∑ i, lam i * (inner ℝ θ (H.get i).1 - (H.get i).2)| ≤ ϵ * ∑ i, |lam i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [abs_mul]
    have := hH (H.get i) (List.get_mem H i)
    unfold SampleCorrect at this
    nlinarith [abs_nonneg (lam i)]
  have hP := hlam
  unfold PredictsWith at hP
  rw [← hv] at hP
  have htot : |inner ℝ θ u - estimate H lam| ≤ 1 / (8 * (T : ℝ)) := by
    rw [hdecomp]
    refine (abs_add_le _ _).trans ?_
    linarith
  rw [abs_sub_le_iff] at htot
  constructor <;> linarith [htot.1, htot.2]
