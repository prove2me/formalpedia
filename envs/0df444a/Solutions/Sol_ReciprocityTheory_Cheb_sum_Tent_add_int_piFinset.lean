-- Prove2me | solution 1 for ReciprocityTheory.Cheb.sum_Tent_add_int_piFinset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:12.3878+00:00
-- url     : https://prove2.me/submissions/aae315fa-9587-41c7-bdcd-a7e2e3cdc67b

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
import Theorems.Thm_ReciprocityTheory_Cheb_sum_tent_add_int_pair

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
theorem _root_.solution [DecidableEq ι] (y : ι → ℝ) :
    ∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), Tent (fun i => y i + n i) = 1 := by
  classical
  show ∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), ∏ i, tent (y i + n i) = 1
  rw [← Finset.prod_univ_sum (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)) (fun i n => tent (y i + n))]
  exact prod_eq_one fun i _ => sum_tent_add_int_pair (y i)
end ReciprocityTheory.Cheb
