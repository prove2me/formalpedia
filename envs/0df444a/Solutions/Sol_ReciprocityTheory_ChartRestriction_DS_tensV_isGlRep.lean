-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tensV_isGlRep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:02.217648+00:00
-- url     : https://prove2.me/submissions/0aa9fca2-8ff8-4a06-82a7-891697f833f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tensV_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isGlRep_apply_swap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ite_end_coord

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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (tensV E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [LinearMap.sub_apply, Pi.sub_apply, Module.End.mul_apply, tensV_coord, map_add,
    isGlRep_apply_swap hE a b c d, ite_end_coord]
  split_ifs <;> subst_vars <;>
    simp only [map_zero, add_zero, sub_zero, zero_sub, sub_self] <;> abel
end ReciprocityTheory.ChartRestriction.DS
