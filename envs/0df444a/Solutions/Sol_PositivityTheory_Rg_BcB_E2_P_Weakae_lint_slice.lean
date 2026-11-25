-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Weakae.lint_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:17.149805+00:00
-- url     : https://prove2.me/submissions/ba24006b-0f78-40e2-9855-8197e00b1a0f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Weakae

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
open PositivityTheory.Rg.BcB.E2.P.Weakae
variable {Y S : Type} [MeasurableSpace Y] [MeasurableSpace S]
namespace PositivityTheory.Rg.BcB.E2.P.Weakae
theorem _root_.solution (ν : Measure S) [IsFiniteMeasure ν] (F : Lp ℂ 2 ν) (f : S → ℂ) (hf : f =ᵐ[ν] F) :
    ∫⁻ s, ‖f s‖ₑ ∂ν ≤ ‖F‖ₑ * ν Set.univ ^ (1 / 2 : ℝ) := by
  rw [← eLpNorm_one_eq_lintegral_enorm, eLpNorm_congr_ae hf, Lp.enorm_def]
  have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := ν) (f := (F : S → ℂ))
    (by norm_num) (Lp.aestronglyMeasurable F)
  convert this using 3
  norm_num
end PositivityTheory.Rg.BcB.E2.P.Weakae
