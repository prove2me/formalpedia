-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.zMat_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:14.678974+00:00
-- url     : https://prove2.me/submissions/4c953af3-2547-49f6-8803-b31794b310f4

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_smul

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
theorem _root_.solution (N : ℕ) (z : Pairs N → ℂ) (s : ℝ) :
    zMat N (s • z) = (s : ℂ) • zMat N z := by
  rw [← zMat_smul]
  congr 1
end ReciprocityTheory.AnForm.P
