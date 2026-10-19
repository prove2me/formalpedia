-- Prove2me | solution 1 for SoficGroups.KunCommonRankArcInvariance.exists_maximizing_partition_ranks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/15c184b1-eaef-401d-9ac7-bd46132bbab4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_maximal_componentRankMass

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCommonRankArcInvariance
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunCommonRankArcInvariance
theorem _root_.solution
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (b : (n : ℕ) → V n → ℤ) :
    ∃ j : (n : ℕ) → Finset (V n) → ℤ,
      ∀ n C, C ∈ (P n).parts →
        j n C ∈ C.image (b n) ∧
          ∀ k ∈ C.image (b n),
            SoficGroups.componentRankMass C (b n) k ≤
              SoficGroups.componentRankMass C (b n) (j n C) := by
  classical
  let j : (n : ℕ) → Finset (V n) → ℤ := fun n C =>
    if h : C.Nonempty then
      (SoficGroups.exists_maximal_componentRankMass
        C (b n) h).choose
    else 0
  refine ⟨j, ?_⟩
  intro n C hC
  have hn : C.Nonempty := (P n).nonempty_of_mem_parts hC
  have h := (SoficGroups.exists_maximal_componentRankMass
    C (b n) hn).choose_spec
  simpa only [j, dif_pos hn] using h
end SoficGroups.KunCommonRankArcInvariance
