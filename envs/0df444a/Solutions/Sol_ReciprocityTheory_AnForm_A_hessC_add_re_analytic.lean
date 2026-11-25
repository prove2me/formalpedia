-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessC_add_re_analytic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:25:03.725396+00:00
-- url     : https://prove2.me/submissions/2749ec2b-72bd-4c9f-8ef8-d3a0e39f7be7

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_add_re_analytic__51ad31de6cad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Matrix
noncomputable section
variable {D E : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (φ : (Fin D → ℂ) → ℝ) (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => φ w + (G w).re) z = hessC φ z := by
  exact hessC_add_re_analytic' φ G z hφ hG
end ReciprocityTheory.AnForm.A
