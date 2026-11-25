-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mixedCof_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:56.883235+00:00
-- url     : https://prove2.me/submissions/d0580c3c-1894-4cdd-954d-113861a2b6ec

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_mixedCof_diag__b2efbf315574

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j : Fin (n + 1)) :
    mixedCof B j j = (1 / ((n + 1 : ℕ) : ℂ)) *
      mdisc (fun i => (B i).submatrix j.succAbove j.succAbove) := by
  exact mixedCof_diag' B j
end ReciprocityTheory.AnForm.A
