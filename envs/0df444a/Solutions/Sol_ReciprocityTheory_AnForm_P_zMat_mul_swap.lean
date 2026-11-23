-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.zMat_mul_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:40.758915+00:00
-- url     : https://prove2.me/submissions/00626f2d-e81d-4112-bb8c-eee244a285a6

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_eq_zero_of_le

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
theorem _root_.solution (N : ℕ) (z : Pairs N → ℂ) (i j : Fin N) :
    zMat N z i j * zMat N z j i = 0 := by
  rcases le_total i j with h | h
  · rw [zMat_eq_zero_of_le z h, zero_mul]
  · rw [zMat_eq_zero_of_le z h, mul_zero]
end ReciprocityTheory.AnForm.P
