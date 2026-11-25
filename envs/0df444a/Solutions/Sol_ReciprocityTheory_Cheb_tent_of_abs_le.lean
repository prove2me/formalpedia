-- Prove2me | solution 1 for ReciprocityTheory.Cheb.tent_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:42.387379+00:00
-- url     : https://prove2.me/submissions/a973c00f-2326-45ec-8032-ae5801d73fa6

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub

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
theorem _root_.solution {t : ℝ} (h : |t| ≤ 1) : tent t = 1 - |t| :=
  max_eq_right (by linarith)
end ReciprocityTheory.Cheb
