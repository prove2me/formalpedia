-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.factorAd_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:12.103918+00:00
-- url     : https://prove2.me/submissions/cc760e58-5ab9-4067-b414-11dab314a36d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_swFst_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_swSnd_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) (i : Fin k) (a b : Fin n) (F G : Big n k M) :
    inner ℂ (factorAd k i a b F) G = inner ℂ F (factorAd k i b a G) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [factorAd_apply, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib]
  congr 1
  · rw [← Equiv.sum_comp (swFst i a b)]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [swFst_apply]
    simp only [Function.update_self, Function.update_idem]
    by_cases h : (κ i).1 = b
    · have hκ : Function.update κ i (b, (κ i).2) = κ := by
        conv_rhs => rw [← Function.update_eq_self i κ]
        rw [← h]
      rw [if_pos (by rw [h, Equiv.swap_apply_right]), if_pos h, hκ, h, Equiv.swap_apply_right]
    · have h' : Equiv.swap a b (κ i).1 ≠ a := by
        rwa [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
      rw [if_neg h', if_neg h, inner_zero_left, inner_zero_right]
  · rw [← Equiv.sum_comp (swSnd i a b)]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [swSnd_apply]
    simp only [Function.update_self, Function.update_idem]
    by_cases h : (κ i).2 = a
    · have hκ : Function.update κ i ((κ i).1, a) = κ := by
        conv_rhs => rw [← Function.update_eq_self i κ]
        rw [← h]
      rw [if_pos (by rw [h, Equiv.swap_apply_left]), if_pos h, hκ, h, Equiv.swap_apply_left]
    · have h' : Equiv.swap a b (κ i).2 ≠ b := by
        rwa [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
      rw [if_neg h', if_neg h, inner_zero_left, inner_zero_right]
end ReciprocityTheory.ChartRestriction.DS
