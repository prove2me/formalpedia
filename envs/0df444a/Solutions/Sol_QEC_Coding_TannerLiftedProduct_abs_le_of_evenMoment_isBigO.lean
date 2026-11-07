-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.abs_le_of_evenMoment_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:13:20.520502+00:00
-- url     : https://prove2.me/submissions/02b4b922-570a-426a-ac74-277b7fd86259

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_of_forall_gt_evenPow_isBigO

set_option autoImplicit false
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {I : Type*} [Fintype I] (eigenvalue : I → ℝ)
    {r : ℝ} (hr : 0 ≤ r)
    (hMoment : ∀ s : ℝ, r < s →
      (fun n : ℕ => ∑ i, |eigenvalue i| ^ (2 * n)) =O[atTop]
        fun n : ℕ => s ^ (2 * n)) :
    ∀ i, |eigenvalue i| ≤ r := by
  classical
  intro i
  apply abs_le_of_forall_gt_evenPow_isBigO hr
  intro s hrs
  have hTerm : (fun n : ℕ => |eigenvalue i| ^ (2 * n)) =O[atTop]
      fun n : ℕ => ∑ j, |eigenvalue j| ^ (2 * n) := by
    apply isBigO_of_le atTop
    intro n
    rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _),
      Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ =>
        pow_nonneg (abs_nonneg _) _)]
    exact Finset.single_le_sum
      (fun j _hj => pow_nonneg (abs_nonneg (eigenvalue j)) _)
      (Finset.mem_univ i)
  exact hTerm.trans (hMoment s hrs)
end QEC.Coding.TannerLiftedProduct
