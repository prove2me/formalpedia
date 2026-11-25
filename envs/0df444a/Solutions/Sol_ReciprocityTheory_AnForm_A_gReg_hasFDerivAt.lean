-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.gReg_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:15.242152+00:00
-- url     : https://prove2.me/submissions/ada8ca2e-94e9-4e8c-9554-f8e6571c7cba

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff

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
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) :
    HasFDerivAt (gReg ε) ((‖ζ‖ ^ 2 + ε)⁻¹ • innerSL ℝ ζ) ζ := by
  have hs : ‖ζ‖ ^ 2 + ε ≠ 0 := by positivity
  have h1 := ((hasStrictFDerivAt_norm_sq ζ).hasFDerivAt.add_const ε).log hs
  have h2 : HasFDerivAt (gReg ε) ((1 / 2 : ℝ) • ((‖ζ‖ ^ 2 + ε)⁻¹ • (2 • innerSL ℝ ζ))) ζ :=
    h1.const_mul (1 / 2 : ℝ)
  refine h2.congr_fderiv ?_
  module
end ReciprocityTheory.AnForm.A
