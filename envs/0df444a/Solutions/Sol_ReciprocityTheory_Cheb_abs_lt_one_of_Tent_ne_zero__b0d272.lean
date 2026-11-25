-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_lt_one_of_Tent_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:52.516403+00:00
-- url     : https://prove2.me/submissions/a7119cb3-a16c-4018-857e-9e541e1b56f9

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
import Theorems.Thm_ReciprocityTheory_Cheb_abs_lt_one_of_tent_ne_zero

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
theorem _root_.solution {y : ι → ℝ} (h : Tent y ≠ 0) (i : ι) : |y i| < 1 :=
  abs_lt_one_of_tent_ne_zero fun h' => h (prod_eq_zero (mem_univ i) h')
end ReciprocityTheory.Cheb
