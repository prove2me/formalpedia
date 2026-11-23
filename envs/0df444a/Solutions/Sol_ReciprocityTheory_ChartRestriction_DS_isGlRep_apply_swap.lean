-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isGlRep_apply_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:59.374801+00:00
-- url     : https://prove2.me/submissions/5b341da7-7ebe-49b1-b106-f2ba83fb6aae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV

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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b c d : Fin n) (v : M) :
    E a b (E c d v) = E c d (E a b v) + ((if b = c then E a d v else 0) - (if d = a then E c b v else 0)) := by
  have h := LinearMap.congr_fun (hE a b c d) v
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add'] at h
  rw [h]; congr 1
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS
