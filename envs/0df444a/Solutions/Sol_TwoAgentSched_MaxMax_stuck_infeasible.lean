-- Prove2me | solution 1 for TwoAgentSched.MaxMax.stuck_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:46:52.592359+00:00
-- url     : https://prove2.me/submissions/621479fa-d39f-41b8-be7d-454d73565b3e

import Mathlib
import Definitions.Def_TwoAgentSched_MaxMax_Model

set_option autoImplicit false
open TwoAgentSched.MaxMax

lemma tas_aux {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j) (l : List ι)
    (hnd : l.Nodup) (U : Finset ι) (hU : U.Nonempty) (hUl : ∀ x ∈ U, x ∈ l) :
    ∃ k ∈ U, ∑ j ∈ U, p j ≤ MooreLateJobs.Shared.completionTime p l k := by
  obtain ⟨k, hkU, hkmax⟩ := Finset.exists_max_image U (fun j => l.idxOf j) hU
  refine ⟨k, hkU, ?_⟩
  have hsub : U ⊆ (l.take (l.idxOf k + 1)).toFinset := by
    intro x hx
    rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt (hUl x hx)]
    have := hkmax x hx
    omega
  unfold MooreLateJobs.Shared.completionTime MooreLateJobs.Shared.completionAt
  calc ∑ j ∈ U, p j ≤ ∑ j ∈ (l.take (l.idxOf k + 1)).toFinset, p j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hp i)
    _ = ((l.take (l.idxOf k + 1)).map p).sum :=
        List.sum_toFinset p (hnd.sublist (List.take_sublist _ _))

theorem solution {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (U : Finset (Job nA nB)) (hU : U.Nonempty) (hUA : ∀ h : Fin nA, Sum.inl h ∉ U)
    (hUB : ∀ k : Fin nB, Sum.inr k ∈ U → Q < fB k (∑ j ∈ U, p j)) :
    ¬ ∃ l : List (Job nA nB), IsFeasible p fB Q l := by
  rintro ⟨l, ⟨hnd, hmem⟩, hfe⟩
  obtain ⟨j, hjU, hsum⟩ := tas_aux p hp l hnd U hU (fun x _ => (hmem x).2 (Finset.mem_univ x))
  rcases j with h | k
  · exact absurd hjU (hUA h)
  · have h1 := hUB k hjU
    have h2 := hfe k
    have h3 := hfB k hsum
    linarith
