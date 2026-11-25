-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_lt_one_of_tent_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:59.081601+00:00
-- url     : https://prove2.me/submissions/56037277-38ec-48a5-81e7-f8a666bd4344

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
import Theorems.Thm_ReciprocityTheory_Cheb_tent_of_one_le_abs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {t : ℝ} (h : tent t ≠ 0) : |t| < 1 := by
  by_contra h'
  exact h (tent_of_one_le_abs (not_lt.mp h'))
end ReciprocityTheory.Cheb
