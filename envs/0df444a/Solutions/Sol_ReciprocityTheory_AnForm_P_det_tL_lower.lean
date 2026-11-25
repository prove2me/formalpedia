-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.det_tL_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:19.947501+00:00
-- url     : https://prove2.me/submissions/e9549ad1-fc7d-4b59-86ad-b52414af7178

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_eq_zero_of_le
import Theorems.Thm_ReciprocityTheory_AnForm_P_castLE_le

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
theorem _root_.solution (N m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) : (tL (Zm N m hm v)).det = 1 := by
  rw [det_of_isLowerTriangular]
  · exact Finset.prod_eq_one fun i _ => by simp [tL, Zm, zMat_eq_zero_of_le v le_rfl]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp [tL, Zm, Matrix.one_apply, hij'.ne, zMat_eq_zero_of_le v (castLE_le hm hij'.le)]
end ReciprocityTheory.AnForm.P
