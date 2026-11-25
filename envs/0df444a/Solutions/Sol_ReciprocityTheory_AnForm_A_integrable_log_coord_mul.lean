-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integrable_log_coord_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:25:07.548266+00:00
-- url     : https://prove2.me/submissions/8f404674-e1ce-4489-84c2-011c0e8a2d48

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Theorems.Thm_ReciprocityTheory_AnForm_A_locallyIntegrable_comp_eval_fin
import Theorems.Thm_ReciprocityTheory_AnForm_A_logNormLocIntC_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Laplacian Pointwise
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (j : Fin (D + 1)) {φ : (Fin (D + 1) → ℂ) → ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * φ z) := by
  have hl : LocallyIntegrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖) volume :=
    locallyIntegrable_comp_eval_fin j logNormLocIntC_thm
  simpa only [smul_eq_mul] using hl.integrable_smul_right_of_hasCompactSupport hφ hs
end ReciprocityTheory.AnForm.A
