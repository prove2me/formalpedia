-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.zMat_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:02.447227+00:00
-- url     : https://prove2.me/submissions/ec21c752-a748-4dbd-b8d5-7e672d983a16

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
theorem _root_.solution {N : ℕ} (z : Pairs N → ℂ) {i j : Fin N} (h : i ≤ j) :
    zMat N z i j = 0 := by
  rw [zMat_apply, dif_neg (not_lt.2 h)]
end ReciprocityTheory.AnForm.P
