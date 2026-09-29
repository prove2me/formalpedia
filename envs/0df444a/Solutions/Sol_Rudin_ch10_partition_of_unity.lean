-- Prove2me | solution 1 for Rudin.ch10_partition_of_unity
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:38:58.182336+00:00
-- url     : https://prove2.me/submissions/025f3e53-c17c-4b67-bb6d-85b7637fcebd

import Mathlib.Topology.PartitionOfUnity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.EquivFin
open Filter Topology


/-- Rudin, Theorem 10.8 (partitions of unity): if `K` is a compact subset of `ℝⁿ` covered by
open sets `V i`, there are finitely many continuous functions `ψ j` with compact support, each
supported in one of the `V i`, with `0 ≤ ψ j`, `∑ ψ j = 1` on `K` and `∑ ψ j ≤ 1`
everywhere. -/
theorem solution (n : ℕ) (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (ι : Type) (V : ι → Set (Fin n → ℝ)) (hV : ∀ i, IsOpen (V i)) (hcover : K ⊆ ⋃ i, V i) :
    ∃ (s : ℕ) (ψ : Fin s → (Fin n → ℝ) → ℝ) (idx : Fin s → ι),
      (∀ j, Continuous (ψ j)) ∧ (∀ j, ∀ x, 0 ≤ ψ j x) ∧
      (∀ j, HasCompactSupport (ψ j)) ∧ (∀ j, tsupport (ψ j) ⊆ V (idx j)) ∧
      (∀ x ∈ K, ∑ j, ψ j x = 1) ∧ (∀ x, ∑ j, ψ j x ≤ 1) := by
  classical
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover V hV hcover
  let e : Fin t.card ≃ {i // i ∈ t} := (Fintype.equivFinOfCardEq (by simp : Fintype.card {i // i ∈ t} = t.card)).symm
  let idx : Fin t.card → ι := fun j => (e j).val
  have hcov : K ⊆ ⋃ j, V (idx j) := by
    intro x hx
    obtain ⟨i,hit,hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨e.symm ⟨i,hit⟩,by simpa [idx] using hxi⟩
  obtain ⟨p,hsub,hcp⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
    hK (fun j => V (idx j)) (fun j => hV (idx j)) (locallyFinite_of_finite _) hcov
  refine ⟨t.card,fun j => p j,idx,fun j => (p j).continuous,?_,hcp,hsub,?_,?_⟩
  · exact fun j x => p.nonneg j x
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one hx
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using p.sum_le_one x


#print axioms solution
