-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_det_jacC_ddf5e32b96d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:51.139295+00:00
-- url     : https://prove2.me/submissions/a92a4333-4ec0-4c60-a141-e9e183b73308

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_of_differentiableOn_e92ad055eb8b

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
noncomputable section
open GroundTheory.Heights₂.Heights.SheetOnlyNull
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SheetOnlyNull
theorem _root_.solution {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) U := by
  intro w hw
  have hF' := (analyticOnNhd_of_differentiableOn hU hF).fderiv w hw
  have hent : ∀ a k, AnalyticAt ℂ (fun z => ReciprocityTheory.AnForm.A.jacC F z a k) w := fun a k => by
    show AnalyticAt ℂ (fun z => fderiv ℂ F z (Pi.single k 1) a) w
    exact (((ContinuousLinearMap.proj a).comp
      (ContinuousLinearMap.apply ℂ (Fin d → ℂ) (Pi.single k (1 : ℂ)))).analyticAt _).comp hF'
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ fun i _ => hent _ _)
end GroundTheory.Heights₂.Heights.SheetOnlyNull
