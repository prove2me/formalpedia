-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.eeVd_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:24.26769+00:00
-- url     : https://prove2.me/submissions/8c714c3e-45c3-48ea-8e9d-e0e7fbf009f6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tensVd_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eeVd_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isGlRep_apply_swap

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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    tensVd E a b * eeVd E = eeVd E * tensVd E a b := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [Module.End.mul_apply, tensVd_coord, eeVd_coord, map_sum, map_neg, map_sub, isGlRep_apply_swap hE a b]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : x = b
  · subst h; simp only [if_true]; abel
  · have h' : ¬ b = x := fun e => h e.symm
    simp only [h, h', if_false, Finset.sum_const_zero, sub_zero, zero_sub]
    abel
end ReciprocityTheory.ChartRestriction.DS
