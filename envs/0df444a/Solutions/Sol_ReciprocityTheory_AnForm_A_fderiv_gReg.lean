-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.fderiv_gReg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:42.959322+00:00
-- url     : https://prove2.me/submissions/8b61d4e2-9548-451e-b7af-e4f1e0d94888

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Theorems.Thm_ReciprocityTheory_AnForm_A_gReg_hasFDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) :
    fderiv ℝ (gReg ε) = fun ζ => (‖ζ‖ ^ 2 + ε)⁻¹ • innerSL ℝ ζ := by
  funext ζ; exact (gReg_hasFDerivAt hε ζ).fderiv
end ReciprocityTheory.AnForm.A
