-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_hessC_add_re_analytic__51ad31de6cad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:15.066408+00:00
-- url     : https://prove2.me/submissions/cb7cf830-6b27-46a3-9a01-b179c8a44688

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_add__d2d06fbdee79
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_re_analytic__40ae417def16

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
theorem _root_.solution (φ : (Fin D → ℂ) → ℝ) (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => φ w + (G w).re) z = hessC φ z := by
  have hΦ : ContDiffAt ℝ 2 (fun w => (G w).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z ((hG.contDiffAt).restrict_scalars ℝ)
  rw [hessC_add' φ _ z hφ hΦ, hessC_re_analytic' G z hG, add_zero]
end ReciprocityTheory.AnForm.A
