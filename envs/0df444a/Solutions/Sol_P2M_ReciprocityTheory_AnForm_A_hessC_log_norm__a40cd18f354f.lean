-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_hessC_log_norm__a40cd18f354f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:47.308947+00:00
-- url     : https://prove2.me/submissions/d5e2d35c-58d0-460e-9250-db088b263b6f

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_congr__aa19fc468bd1
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_re_analytic__40ae417def16
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_re_analytic_eq_log_norm

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
theorem _root_.solution (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hg : AnalyticAt ℂ g z)
    (hz : g z ≠ 0) : hessC (fun w => Real.log ‖g w‖) z = 0 := by
  obtain ⟨G, hG, hEq⟩ := exists_re_analytic_eq_log_norm g z hg hz
  rw [hessC_congr' hEq]
  exact hessC_re_analytic' G z hG
end ReciprocityTheory.AnForm.A
