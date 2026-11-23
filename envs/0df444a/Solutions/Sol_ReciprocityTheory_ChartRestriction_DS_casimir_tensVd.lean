-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimir_tensVd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:36.2838+00:00
-- url     : https://prove2.me/submissions/35f004fc-5994-4edc-b888-392aea5365f6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tensVd_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eeVd_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_diagOp_coord

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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) :
    casimir (tensVd E) = diagOp (casimir E) + (n : ℂ) • 1 + (2 : ℂ) • eeVd E := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [casimir, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, diagOp_coord, eeVd_coord, tensVd_coord, map_sub,
    Module.End.one_apply]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have key : ∀ g : Fin n → Fin n → M, (∑ i, ∑ j, if x = i then g i j else 0) = ∑ j, g x j := by
    intro g
    rw [Finset.sum_eq_single x (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    simp
  rw [key (fun i j => E i j (f j))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul, two_smul]
  abel
end ReciprocityTheory.ChartRestriction.DS
