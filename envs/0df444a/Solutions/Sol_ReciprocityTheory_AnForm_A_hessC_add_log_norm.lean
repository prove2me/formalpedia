-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessC_add_log_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:40.216821+00:00
-- url     : https://prove2.me/submissions/1ac9e510-3c70-4e52-b64a-7d5a7e35aa6d

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_add_log_norm__562736f45a00


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
theorem _root_.solution (φ : (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    hessC (fun w => φ w + Real.log ‖g w‖) z = hessC φ z := by
  exact hessC_add_log_norm' φ g z hφ hg hz
end ReciprocityTheory.AnForm.A
