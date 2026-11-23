-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.zMat_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:47.585305+00:00
-- url     : https://prove2.me/submissions/06062443-1f55-40be-916a-5c1ba1626ba7

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
theorem _root_.solution {N : ℕ} (z : Pairs N → ℂ) (hN : N ≤ 1) : zMat N z = 0 := by
  ext i j
  rw [zMat_apply, dif_neg]
  · rfl
  intro h
  have := Fin.lt_iff_val_lt_val.1 h
  have := i.isLt
  omega
end ReciprocityTheory.AnForm.P
