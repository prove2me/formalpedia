-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_zero_truncExpPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:34.62223+00:00
-- url     : https://prove2.me/submissions/e7bd3d96-08c6-49ab-a2b3-d6924ee2a485

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_cpP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : cf 0 (cpP N A) = 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Subsingleton.elim _ _
  · rw [cf_cpP, if_pos hN]; simp
end ReciprocityTheory.AnForm.P
