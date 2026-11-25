-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegBallMass_proof_fdc7e2a04306
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:57:52.166798+00:00
-- url     : https://prove2.me/submissions/bfe8f0de-2618-4f18-9c42-9663ef996ea3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegFixedBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegBallMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegBallMass_chartDens_indicator_mono_6ce5d838cf83
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegBallMass_measurable_chartDens_indicator_29eab0d92680
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open RegBallMass
namespace GroundTheory.Heights₂.Heights
namespace RegBallMass
theorem _root_.solution (hF : RegFixedBallMass.Statement) (hM : RegLelongMono.Statement)
    (hN : RegDensNonneg.Statement) : RegBallMass.Statement := by
  intro n d J A u K hJ hdim hA hu hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  set c : ℝ := Real.sqrt (n + 1) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  obtain ⟨M, hMb⟩ := hF n d J A u (R₀ + c) hJ hdim hA hu
  refine ⟨max M 0, le_max_right _ _, fun ε hε x hx r hr => ?_⟩
  set F : Set (Fin n → ℂ) → (Fin (d + 1) → ℂ) → ℝ := fun S =>
    chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) with hFdef
  have h1 : Metric.ball x r ⊆ euclBall x (c * r) := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hr.1] at hy
    show Real.sqrt (euclPot (y - x)) < c * r
    rw [Real.sqrt_lt' (mul_pos hc0 hr.1), mul_pow, hc2]
    calc euclPot (y - x) = ∑ j, ‖(y - x) j‖ ^ 2 := rfl
      _ ≤ ∑ _j : Fin n, r ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hy j).le 2
      _ = n * r ^ 2 := by simp
      _ < (n + 1) * r ^ 2 := by nlinarith [pow_pos hr.1 2]
  have h2 : euclBall x c ⊆ Metric.closedBall 0 (R₀ + c) := by
    intro y hy
    have hy' : euclPot (y - x) < c ^ 2 := (Real.sqrt_lt' hc0).1 hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hyx : ‖y - x‖ ≤ c := by
      refine (pi_norm_le_iff_of_nonneg hc0.le).2 fun j => ?_
      have hj : ‖(y - x) j‖ ^ 2 ≤ euclPot (y - x) :=
        Finset.single_le_sum (f := fun j => ‖(y - x) j‖ ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc0.le two_ne_zero).1 (by linarith)
    calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ R₀ + c := add_le_add (hR₀ x hx) hyx
  have h3 : euclBall x (c * r) ⊆ euclBall x c := fun y hy =>
    show Real.sqrt (euclPot (y - x)) < c from
      lt_of_lt_of_le (show Real.sqrt (euclPot (y - x)) < c * r from hy)
        (mul_le_of_le_one_right hc0.le hr.2)
  have hpos : ∀ {S S' : Set (Fin n → ℂ)}, S ⊆ S' → ∀ y, 0 ≤ F S y ∧ F S y ≤ F S' y :=
    fun hS y => chartDens_indicator_mono hN hA u hε.1 hS y
  have hEm : ∀ ρ, MeasurableSet (euclBall x ρ) := fun ρ =>
    (isOpen_lt (((contDiff_euclPot n).continuous.comp
      (continuous_id.sub continuous_const)).sqrt) continuous_const).measurableSet
  obtain ⟨hIR, hIRle⟩ := hMb ε hε
  have hint : ∀ S, MeasurableSet S → S ⊆ Metric.closedBall 0 (R₀ + c) → Integrable (F S) :=
    fun S hS hSR => hIR.mono' (measurable_chartDens_indicator hJ hdim hA u hε.1 hS).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpos hSR y).1]; exact (hpos hSR y).2)
  have hBI := hint _ Metric.isOpen_ball.measurableSet (h1.trans (h3.trans h2))
  refine ⟨hBI, ?_⟩
  have hmono := hM n d J A u ε x (c * r) c hJ hdim hA hε.1 (mul_pos hc0 hr.1)
    (mul_le_of_le_one_right hc0.le hr.2)
  have hI1 : ∫ y, F (Metric.ball x r) y ≤ ∫ y, F (euclBall x (c * r)) y :=
    integral_mono hBI (hint _ (hEm _) (h3.trans h2)) fun y => (hpos h1 y).2
  have hI2 : ∫ y, F (euclBall x c) y ≤ ∫ y, F (Metric.closedBall 0 (R₀ + c)) y :=
    integral_mono (hint _ (hEm _) h2) hIR fun y => (hpos h2 y).2
  have hI3 : ∫ y, F (euclBall x (c * r)) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := by
    have : c ^ (2 * d) * ∫ y, F (euclBall x (c * r)) y ≤
        c ^ (2 * d) * (r ^ (2 * d) * ∫ y, F (euclBall x c) y) := by
      rw [← mul_assoc, ← mul_pow]; exact hmono
    exact le_of_mul_le_mul_left this (pow_pos hc0 _)
  calc ∫ y, F (Metric.ball x r) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := hI1.trans hI3
    _ ≤ r ^ (2 * d) * max M 0 :=
      mul_le_mul_of_nonneg_left (hI2.trans (hIRle.trans (le_max_left _ _))) (pow_nonneg hr.1.le _)
    _ = max M 0 * r ^ (2 * d) := mul_comm _ _
end RegBallMass
end GroundTheory.Heights₂.Heights
