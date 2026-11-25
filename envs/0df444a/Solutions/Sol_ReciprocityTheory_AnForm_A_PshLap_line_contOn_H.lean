-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.line_contOn_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:39.830768+00:00
-- url     : https://prove2.me/submissions/88b07347-741b-448d-b0e8-4f55f902e9a3

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (z w : Fin D → ℂ) :
    ContinuousOn (Hc φ z w) {ζ : ℂ | z + ζ • w ∈ U} := by
  have h2 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have h3 : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) U := h2.continuousOn_fderiv_of_isOpen hU le_rfl
  have hl : Continuous (fun ζ : ℂ => z + ζ • w) := by fun_prop
  exact continuousOn_const.clm_comp
    ((h3.comp hl.continuousOn (fun ζ h => h)).clm_comp continuousOn_const)
end ReciprocityTheory.AnForm.A.PshLap
