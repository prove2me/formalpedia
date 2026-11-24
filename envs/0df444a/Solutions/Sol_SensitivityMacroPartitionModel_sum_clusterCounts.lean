-- Prove2me | solution 1 for SensitivityMacroPartitionModel.sum_clusterCounts
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:20.505821+00:00
-- url     : https://prove2.me/submissions/b29547d4-4e88-4217-9b99-3302eb8ec0de

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionCounts
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

namespace SensitivityMacroPartitionModel
end SensitivityMacroPartitionModel

section


/-! Every partition of a finite indexed head set is represented by choosing
its least index in each class. The finite search may enumerate all functions
whose value at index i is at most i; no canonicality test is needed for
completeness. -/
namespace SensitivityMacroPartitionModel

open scoped BigOperators
set_option autoImplicit false



























noncomputable section
open scoped Classical













theorem macro_least {n : ℕ} {M : Type} (cluster : Fin n → M) (i : Fin n) :
    cluster (least cluster i) = cluster i := by
  have hm : least cluster i ∈ fiber cluster i := Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hm).2

theorem least_eq_iff {n : ℕ} {M : Type} (cluster : Fin n → M) (i j : Fin n) :
    least cluster i = least cluster j ↔ cluster i = cluster j := by
  constructor
  · intro h
    simpa only [macro_least] using congrArg cluster h
  · intro h
    have hf : fiber cluster i = fiber cluster j := by simp only [fiber,h]
    unfold least
    congr 1

















end
end SensitivityMacroPartitionModel

end

/-! The counts attached to a cluster are kept once for pricing and once per
guard head for the uncompressed incidence budget. The finite product of
bounded counts includes every actual assignment. -/
open SensitivityMacroPartitionModel
open scoped Classical BigOperators
set_option autoImplicit false
variable {n : ℕ} {M : Type}

theorem solution (cluster : Fin n → M) (G : Finset (Fin n)) (amount : M → ℕ) :
    (∑ k, clusterCounts cluster G amount k) = ∑ m ∈ G.image cluster, amount m := by
  have hi : Set.InjOn cluster (↑(G.image (least cluster)) : Set (Fin n)) := by
    intro i hi j hj h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hj
    apply (least_eq_iff cluster a b).mpr
    simpa only [macro_least] using h
  have heq : (G.image (least cluster)).image cluster = G.image cluster := by
    simp only [Finset.image_image,Function.comp_def,macro_least]
  calc
    (∑ k, clusterCounts cluster G amount k) = ∑ k ∈ G.image (least cluster), amount (cluster k) := by
      simp only [clusterCounts,← Finset.sum_filter]
      congr 1
      ext k
      simp
    _ = ∑ m ∈ (G.image (least cluster)).image cluster, amount m :=
      (Finset.sum_image hi).symm
    _ = ∑ m ∈ G.image cluster, amount m := by rw [heq]
