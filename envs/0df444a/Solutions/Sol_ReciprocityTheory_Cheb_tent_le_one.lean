-- Prove2me | solution 1 for ReciprocityTheory.Cheb.tent_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:56.405797+00:00
-- url     : https://prove2.me/submissions/e05933b3-076a-4dac-bd5a-406a8eeec084

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
theorem _root_.solution (t : ℝ) : tent t ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg t])
end ReciprocityTheory.Cheb
