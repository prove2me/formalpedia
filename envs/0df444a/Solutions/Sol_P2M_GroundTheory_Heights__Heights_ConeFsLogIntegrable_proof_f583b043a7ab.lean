-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFsLogIntegrable_proof_f583b043a7ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:05:43.970908+00:00
-- url     : https://prove2.me/submissions/264a8ec7-77f6-48d4-8995-9350bd3c19cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSlab
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_771c24ca10eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_fsLog_pointOf_le_18b3cd70d7d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLog_norm_le_of_fsLog_le_2952b5d2345d

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
open MvPolynomial MeasureTheory Set Matrix Filter
noncomputable section
open ConeFsLog
namespace GroundTheory.Heights₂.Heights
namespace ConeFsLogIntegrable
theorem _root_.solution (hfin : ConeBallFinite.Statement)
    (hslab : ConeSlabBound.Statement) : ConeFsLogIntegrable.Statement := by
  intro n e h W f u hW hf hu
  have hS := hfin n e h W f hW hf
  obtain ⟨C, α, hα, hC⟩ := hslab n e h W f u hW hf hu
  set μ := (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict (coneBall h W)
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun y => fsLog h u (h.pointOf y) with hFdef
  set M := max (Real.log (h.norm u)) 0
  have hFm : Measurable F := by
    have : F = fun y => Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖) :=
      funext fun y => fsLog_pointOf h u y
    rw [this]
    have hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y) := by
      unfold HermNorm.pointOf; fun_prop
    refine Real.measurable_log.comp (Measurable.div ?_ measurable_norm)
    exact (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp hp)).norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun y => max (-F y) 0
  have hGm : Measurable G := hFm.neg.max measurable_const

  have hG : ∫⁻ y, ENNReal.ofReal (G y) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Filter.Eventually.of_forall fun y => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro y ⟨hy, hyS⟩
      refine ⟨hyS, norm_le_of_fsLog_le h u y ?_⟩
      have : t ≤ -F y := by
        rcases le_max_iff.mp (show t ≤ G y from hy) with h1 | h1
        · exact h1
        · linarith
      change F y ≤ -t; linarith
    · rw [← Real.exp_mul]; ring_nf
  refine ⟨hFm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hle : ∀ y, ‖F y‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G y) := by
    intro y
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := fsLog_pointOf_le h u y
    rcases le_or_gt 0 (F y) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F y) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F y) 0; have := le_max_right (Real.log (h.norm u)) 0
      linarith
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS, hG⟩
end ConeFsLogIntegrable
end GroundTheory.Heights₂.Heights
