-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_hessC_re_analytic__40ae417def16
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:08.764617+00:00
-- url     : https://prove2.me/submissions/0a0c0cab-7fc6-42e3-8c70-a54b2a126881

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_eq_zero_of_re_bilin
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv_fderiv_re_analytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Complex Filter Topology
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => (G w).re) z = 0 := hessC_eq_zero_of_re_bilin _ z _ (fderiv_fderiv_re_analytic G z hG)
end ReciprocityTheory.AnForm.A
