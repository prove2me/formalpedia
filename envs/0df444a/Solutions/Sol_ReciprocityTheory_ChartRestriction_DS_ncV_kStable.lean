-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ncV_kStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:16.229815+00:00
-- url     : https://prove2.me/submissions/b729f55c-045f-45fb-bdce-46693c8564f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mem_ncV_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ncV_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ncV_eq_zero

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
theorem _root_.solution (hV : IsKStableSub ε E V) (k : ℕ) :
    IsKStableSub ε (bAct E k) (ncV ε V k) := by
  intro a b hab F hF
  rw [mem_ncV_iff]
  intro κ
  rw [bAct_apply]
  split_ifs with hc
  · refine add_mem (hV a b hab _ (ncV_mem hF κ)) (Submodule.sum_mem _ fun i _ => ?_)
    rw [factorAd_apply]
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs <;>
      first | exact ncV_mem hF _ | exact Submodule.zero_mem _
  · push_neg at hc
    obtain ⟨j, hj⟩ := hc
    rw [Submodule.mem_bot, ncV_eq_zero hF j hj, map_zero, zero_add]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [factorAd_apply]
    by_cases hij : i = j
    · subst hij
      have z1 : (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) = 0 := by
        split_ifs with h1
        · apply ncV_eq_zero hF i
          simp only [Function.update_self]
          rw [← hab, ← h1]
          exact hj
        · rfl
      have z2 : (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) = 0 := by
        split_ifs with h2
        · apply ncV_eq_zero hF i
          simp only [Function.update_self]
          rw [hab, ← h2]
          exact hj
        · rfl
      rw [z1, z2, sub_zero]
    · have hu : ∀ x : Fin n × Fin n, ε ((Function.update κ i x) j).1 = ε ((Function.update κ i x) j).2 := by
        intro x
        rw [Function.update_of_ne (Ne.symm hij)]
        exact hj
      have z1 : (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) = 0 := by
        split_ifs
        · exact ncV_eq_zero hF j (hu _)
        · rfl
      have z2 : (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) = 0 := by
        split_ifs
        · exact ncV_eq_zero hF j (hu _)
        · rfl
      rw [z1, z2, sub_zero]
end ReciprocityTheory.ChartRestriction.DS
