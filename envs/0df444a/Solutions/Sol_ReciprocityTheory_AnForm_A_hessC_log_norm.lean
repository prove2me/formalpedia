-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessC_log_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:43.030122+00:00
-- url     : https://prove2.me/submissions/30c7757a-d0de-4e2e-94e0-4ebb27c5adbe

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_log_norm__a40cd18f354f


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
theorem _root_.solution (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hg : AnalyticAt ℂ g z)
    (hz : g z ≠ 0) : hessC (fun w => Real.log ‖g w‖) z = 0 := by
  exact hessC_log_norm' g z hg hz
end ReciprocityTheory.AnForm.A
