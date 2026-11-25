-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_two_truncExpPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:15.104293+00:00
-- url     : https://prove2.me/submissions/ba479175-e163-441f-82c1-fbc54d7e0037

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
theorem _root_.solution (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : ∃ c : ℂ, cf 2 (cpP N A) = c • A ^ 2 := by
  rw [cf_cpP]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, by simp⟩
end ReciprocityTheory.AnForm.P
