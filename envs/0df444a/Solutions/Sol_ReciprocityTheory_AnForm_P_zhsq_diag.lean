-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.zhsq_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:16.890936+00:00
-- url     : https://prove2.me/submissions/7aa53fbf-6a89-4ae1-8414-281b154895f0

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_zsq_diag

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
theorem _root_.solution (N : ℕ) (z : Pairs N → ℂ) (i : Fin N) : ((zMat N z)ᴴ ^ 2) i i = 0 := by
  rw [← conjTranspose_pow, conjTranspose_apply, zsq_diag, star_zero]
end ReciprocityTheory.AnForm.P
