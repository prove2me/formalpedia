-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeDeepMass_proof_e875112c7a13
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:08:33.262149+00:00
-- url     : https://prove2.me/submissions/296080a0-6ca9-4813-a0c6-a5181c1cec52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepAreaCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_poincareDeepWeight_0baadc7caca3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tubeDeep_term_0355a045511e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_tubeDens_109588edc399
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tubeDens_nonneg_84f1fc7d5825


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
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace TubeDeepMass
theorem _root_.solution (hR : TubeDeepRankOne.Statement) (hC : TubeDeepAreaCount.Statement)
    (hW : TubeDeepWeightMass.Statement) : TubeDeepMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  have hc0 : 0 ≤ (2 / Real.pi) ^ (d + 1) := by positivity
  set g : (Fin (d + 1) → ℂ) → ℝ := fun z => (2 / Real.pi) ^ (d + 1) * poincareDeepWeight (z 0) with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z =>
    mul_nonneg hc0 (by unfold poincareDeepWeight; split_ifs <;> positivity)
  have hgm : Measurable g :=
    measurable_const.mul (measurable_poincareDeepWeight.comp (measurable_pi_apply 0))
  have hl : Measurable (logAbsSq P) :=
    ((continuous_norm.comp (MvPolynomial.continuous_eval P)).pow 2).measurable.log
  have hF : ∀ y, {y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y =
      sheetSum J A (fun x s => (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y := by
    intro y
    by_cases hy : logAbsSq P y < -Real.exp 1
    · rw [Set.indicator_of_mem (show y ∈ {y | logAbsSq P y < -Real.exp 1} from hy), tubeDens, chartAbsDens, sheetSum, sheetSum]
      refine finsum_congr fun x => finsum_congr fun hx => ?_
      split_ifs with h
      · exact tubeDeep_term hR hx h.choose_spec hy
      · rfl
    · rw [Set.indicator_of_notMem (show y ∉ {y | logAbsSq P y < -Real.exp 1} from hy)]
      have hw0 : ∀ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (I : Fin d → Fin n), g (deepMap P s I y) = 0 := by
        intro s I
        simp only [hg, deepMap, Matrix.cons_val_zero, poincareDeepWeight]
        exact mul_eq_zero_of_right _ (if_neg hy)
      simp [sheetSum, hw0]
  obtain ⟨N, hN⟩ := hC n d J A P R hJ hdim hA
  refine ⟨((measurable_tubeDens hA P R _).indicator (measurableSet_lt hl measurable_const)).aestronglyMeasurable,
    ?_⟩
  have hnn : ∀ y, 0 ≤ {y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y :=
    fun y => Set.indicator_nonneg (fun y _ => tubeDens_nonneg J A P R _ y) y
  show ∫⁻ y, ‖{y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)) y‖ₑ < ⊤
  calc _ = ∫⁻ y, ENNReal.ofReal (sheetSum J A (fun x s =>
          (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
            ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y) :=
        lintegral_congr fun y => by rw [Real.enorm_eq_ofReal (hnn y), hF y]
    _ ≤ (N : ℝ≥0∞) * ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R}, ENNReal.ofReal (g z) :=
        hN g hgm hg0
    _ = (N : ℝ≥0∞) * (ENNReal.ofReal ((2 / Real.pi) ^ (d + 1)) *
          ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R},
            ENNReal.ofReal (poincareDeepWeight (z 0))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact congrArg _ (lintegral_congr fun z => ENNReal.ofReal_mul hc0)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top N)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hW d R))
end TubeDeepMass
end GroundTheory.Heights₂.Heights
