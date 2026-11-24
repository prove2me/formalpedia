-- Prove2me | solution 1 for ReciprocityTheory.Cheb.Tent_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:54.967155+00:00
-- url     : https://prove2.me/submissions/16bd983a-bd55-4609-ab14-c889448ec04e

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
import Theorems.Thm_ReciprocityTheory_Cheb_tent_nonneg

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
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (y : ι → ℝ) : 0 ≤ Tent y := prod_nonneg fun _ _ => tent_nonneg _
end ReciprocityTheory.Cheb
