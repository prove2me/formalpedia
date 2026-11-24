-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.eeV_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:22.490897+00:00
-- url     : https://prove2.me/submissions/22170522-85e3-4167-9505-6a77d69f880f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tensV_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eeV_coord
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
    tensV E a b * eeV E = eeV E * tensV E a b := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [Module.End.mul_apply, tensV_coord, eeV_coord, map_sum, map_add, isGlRep_apply_swap hE a b]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : x = a
  · subst h; simp only [if_true]; abel
  · simp only [h, if_false, Finset.sum_const_zero, sub_zero, add_zero]
end ReciprocityTheory.ChartRestriction.DS
