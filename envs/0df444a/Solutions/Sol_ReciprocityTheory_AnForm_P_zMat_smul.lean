-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.zMat_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:48.048856+00:00
-- url     : https://prove2.me/submissions/52b7447a-1726-48dd-8f28-08457a0f9315

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_apply

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
theorem _root_.solution (N : ℕ) (z : Pairs N → ℂ) (c : ℂ) : zMat N (c • z) = c • zMat N z := by
  ext i j
  rw [zMat_apply, Matrix.smul_apply, zMat_apply]
  split_ifs <;> simp
end ReciprocityTheory.AnForm.P
