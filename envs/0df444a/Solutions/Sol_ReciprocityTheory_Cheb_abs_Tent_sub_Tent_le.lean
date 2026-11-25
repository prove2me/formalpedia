-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_Tent_sub_Tent_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:48:07.825934+00:00
-- url     : https://prove2.me/submissions/445d63c5-0510-45ad-b0f5-c796afda4f95

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
import Theorems.Thm_ReciprocityTheory_Cheb_tent_nonneg
import Theorems.Thm_ReciprocityTheory_Cheb_tent_le_one
import Theorems.Thm_ReciprocityTheory_Cheb_abs_tent_sub_tent_le__c56d69
import Theorems.Thm_ReciprocityTheory_Cheb_abs_prod_sub_prod_le_sum_abs_sub

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
theorem _root_.solution (y y' : ι → ℝ) : |Tent y - Tent y'| ≤ ∑ i, |y i - y' i| := by
  unfold Tent
  refine (abs_prod_sub_prod_le_sum_abs_sub univ _ _ (fun i _ => ?_) (fun i _ => ?_)).trans
    (sum_le_sum fun i _ => abs_tent_sub_tent_le (y i) (y' i))
  · rw [abs_of_nonneg (tent_nonneg _)]; exact tent_le_one _
  · rw [abs_of_nonneg (tent_nonneg _)]; exact tent_le_one _
end ReciprocityTheory.Cheb
