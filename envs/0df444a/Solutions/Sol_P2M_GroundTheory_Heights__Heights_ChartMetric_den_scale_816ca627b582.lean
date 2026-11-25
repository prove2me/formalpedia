-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMetric_den_scale_816ca627b582
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:51:54.621878+00:00
-- url     : https://prove2.me/submissions/495e2ef4-0d81-48e5-b5ee-8c4f2f99646f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_NormSqEvalConeScale
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_norm_sq_evalCone_scale_efe510351eca

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMetric
namespace GroundTheory.Heights₂.Heights.ChartMetric
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
    (D : AddBlockData P) {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {r : ℕ} {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ}
    (hG : P.IsHomogGenerators G δ) (t : ι → ℂ) (ht : ∀ k, t k ≠ 0) (z : Cone n ℂ) :
    D.den d g G δ (fun k i ↦ t k * z k i) =
      (∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k))) * D.den d g G δ z := by
  have ht' : ∀ k, ‖t k‖ ≠ 0 := fun k ↦ norm_ne_zero_iff.mpr (ht k)
  unfold AddBlockData.den
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    obtain ⟨e, he, hed⟩ := hg.homog c j
    rw [norm_sq_evalCone_scale t z he]
    simp only [hed]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [norm_sq_evalCone_scale t z (hG.homog i)]
    have hl : ∀ k, l2Norm (fun j ↦ t k * z k j) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) =
        ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) * l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) :=
      fun k ↦ by rw [vectorL2Norm_const_mul, mul_zpow]
    simp only [hl, Finset.prod_mul_distrib]
    have hs : (∏ k, ‖t k‖ ^ (2 * (δ i k : ℤ))) * ∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) =
        ∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← zpow_add₀ (ht' k)]
      congr 1
      ring
    rw [← hs]
    ring
end GroundTheory.Heights₂.Heights.ChartMetric
