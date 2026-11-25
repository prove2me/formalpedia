-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_one_truncExpPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:18:53.451364+00:00
-- url     : https://prove2.me/submissions/32083b67-77dc-4d21-aa31-f12e523e03ac

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
theorem _root_.solution (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (hA : N ≤ 1 → A = 0) :
    cf 1 (cpP N A) = A := by
  rw [cf_cpP]
  split_ifs with h
  · simp
  · exact (hA (by omega)).symm
end ReciprocityTheory.AnForm.P
