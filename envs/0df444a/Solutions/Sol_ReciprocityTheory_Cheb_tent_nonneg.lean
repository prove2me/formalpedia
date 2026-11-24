-- Prove2me | solution 1 for ReciprocityTheory.Cheb.tent_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:37.589581+00:00
-- url     : https://prove2.me/submissions/a08e39f3-de80-4be8-8973-653b5f264e36

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
theorem _root_.solution (t : ℝ) : 0 ≤ tent t := le_max_left _ _
end ReciprocityTheory.Cheb
