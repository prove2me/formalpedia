-- Prove2me | solution 1 for ReciprocityTheory.Cheb.Tent_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:39.13924+00:00
-- url     : https://prove2.me/submissions/406877dd-edd9-45c2-8c86-662868174792

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
import Theorems.Thm_ReciprocityTheory_Cheb_tent_nonneg
import Theorems.Thm_ReciprocityTheory_Cheb_tent_le_one

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
theorem _root_.solution (y : ι → ℝ) : Tent y ≤ 1 :=
  prod_le_one (fun _ _ => tent_nonneg _) (fun _ _ => tent_le_one _)
end ReciprocityTheory.Cheb
