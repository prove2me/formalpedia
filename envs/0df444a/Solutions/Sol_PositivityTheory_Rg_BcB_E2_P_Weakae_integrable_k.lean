-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Weakae.integrable_k
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:05.921498+00:00
-- url     : https://prove2.me/submissions/2de37f75-4736-48be-b6d9-416e17fb133f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Weakae
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Weakae_lint_slice

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
theorem _root_.solution (m : Measure Y) [SFinite m] (ν : Measure S) [IsFiniteMeasure ν]
    (F : Y → Lp ℂ 2 ν) (f : Y → S → ℂ) (c : Y → ℂ) (hf : IsRep F f) (hc : AEStronglyMeasurable c m)
    (hint : ∫⁻ y, ‖c y‖ₑ * ‖F y‖ₑ ∂m ≠ ⊤) :
    Integrable (fun p : Y × S => c p.1 * conj (f p.1 p.2)) (m.prod ν) := by
  have hcm : AEStronglyMeasurable (fun p : Y × S => c p.1) (m.prod ν) := hc.comp_fst
  have hfm : AEStronglyMeasurable (fun p : Y × S => conj (f p.1 p.2)) (m.prod ν) :=
    (Complex.continuous_conj.measurable.comp hf.1).aestronglyMeasurable
  refine ⟨hcm.mul hfm, ?_⟩
  show ∫⁻ p, ‖c p.1 * conj (f p.1 p.2)‖ₑ ∂(m.prod ν) < ⊤
  have hm : AEMeasurable (fun p : Y × S => ‖c p.1 * conj (f p.1 p.2)‖ₑ) (m.prod ν) :=
    (hcm.mul hfm).enorm
  rw [lintegral_prod _ hm]
  have hC : ν Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top ν _)
  calc ∫⁻ y, ∫⁻ s, ‖c (y, s).1 * conj (f (y, s).1 (y, s).2)‖ₑ ∂ν ∂m
      = ∫⁻ y, ‖c y‖ₑ * ∫⁻ s, ‖f y s‖ₑ ∂ν ∂m := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        refine lintegral_congr fun s => ?_
        simp [enorm_mul]
    _ ≤ ∫⁻ y, ‖c y‖ₑ * (‖F y‖ₑ * ν Set.univ ^ (1 / 2 : ℝ)) ∂m := by
        refine lintegral_mono fun y => ?_
        gcongr
        exact lint_slice ν (F y) (f y) (hf.2 y)
    _ = (∫⁻ y, ‖c y‖ₑ * ‖F y‖ₑ ∂m) * ν Set.univ ^ (1 / 2 : ℝ) := by
        simp_rw [← mul_assoc]
        exact lintegral_mul_const' _ _ hC
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hint) (lt_top_iff_ne_top.2 hC)
end PositivityTheory.Rg.BcB.E2.P.Weakae
