-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.line_hasFDerivAt_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:36.406735+00:00
-- url     : https://prove2.me/submissions/ce6bf307-e915-40e3-8dd0-50f79e8e4269

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_complexLine_apply
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_Pc_apply
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_hasFDerivAt_line

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
theorem _root_.solution (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (z w : Fin D → ℂ) {ζ : ℂ}
    (hζ : z + ζ • w ∈ U) : HasFDerivAt (fun ζ : ℂ => φ (z + ζ • w)) (Gc φ z w ζ) ζ := by
  have hd : HasFDerivAt φ (fderiv ℝ φ (z + ζ • w)) (z + ζ • w) :=
    ((hφ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hζ)).hasFDerivAt
  refine (hd.comp ζ (hasFDerivAt_line z w ζ)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun a => ?_
  simp [Gc, Pc_apply, complexLine_apply]
end ReciprocityTheory.AnForm.A.PshLap
