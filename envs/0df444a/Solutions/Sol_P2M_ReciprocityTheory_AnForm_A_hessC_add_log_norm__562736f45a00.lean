-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_hessC_add_log_norm__562736f45a00
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:58.356293+00:00
-- url     : https://prove2.me/submissions/98ae472a-57b9-42dc-8198-52594e3012e4

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_congr__aa19fc468bd1
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_add_re_analytic__51ad31de6cad
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
theorem _root_.solution (φ : (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    hessC (fun w => φ w + Real.log ‖g w‖) z = hessC φ z := by
  obtain ⟨G, hG, hEq⟩ := exists_re_analytic_eq_log_norm g z hg hz
  have h2 : (fun w => φ w + Real.log ‖g w‖) =ᶠ[𝓝 z] fun w => φ w + (G w).re :=
    hEq.mono fun w hw => by simp only [hw]
  rw [hessC_congr' h2]
  exact hessC_add_re_analytic' φ G z hφ hG
end ReciprocityTheory.AnForm.A
