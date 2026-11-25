-- Prove2me | solution 1 for ReciprocityTheory.Cheb.hasSum_Tent_add_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:17:50.783236+00:00
-- url     : https://prove2.me/submissions/41204312-b670-4d93-b88b-928f99dca029

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
import Theorems.Thm_ReciprocityTheory_Cheb_Tent_add_int_eq_zero_of_notMem
import Theorems.Thm_ReciprocityTheory_Cheb_sum_Tent_add_int_piFinset

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
theorem _root_.solution (y : ι → ℝ) : HasSum (fun n : ι → ℤ => Tent (fun i => y i + n i)) 1 := by
  classical
  have h : HasSum (fun n : ι → ℤ => Tent (fun i => y i + n i))
      (∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), Tent (fun i => y i + n i)) :=
    hasSum_sum_of_ne_finset_zero fun n hn => Tent_add_int_eq_zero_of_notMem y hn
  rwa [sum_Tent_add_int_piFinset] at h
end ReciprocityTheory.Cheb
