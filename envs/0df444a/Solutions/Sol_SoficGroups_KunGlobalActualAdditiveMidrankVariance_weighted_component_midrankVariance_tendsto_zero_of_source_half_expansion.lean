-- Prove2me | solution 1 for SoficGroups.KunGlobalActualAdditiveMidrankVariance.weighted_component_midrankVariance_tendsto_zero_of_source_half_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/e8eceeba-71fe-48d8-8384-db061c90cd99

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunGlobalActualAdditiveMidrankVariance_weighted_component_midrankVariance_tendsto_zero_of_additive_expansion

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunGlobalActualAdditiveMidrankVariance
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunGlobalActualAdditiveMidrankVariance
theorem _root_.solution
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (b : (n : ℕ) → V n → ℤ)
    (γ : ℝ) (hγ : 0 < γ)
    (hexpand : ∀ n C, C ∈ (P n).parts → ∀ E : Finset (V n),
      E ⊆ C → 2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (SoficGroups.boundary (σ n) E : ℝ))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            (Fintype.card (V n) : ℝ))
      atTop (nhds 0))
    (henergy : Tendsto
      (fun n =>
        (∑ i : ι, ∑ x : V n,
          (SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank
            (P n) (b n) (σ n i x) -
           SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank
            (P n) (b n) x) ^ 2) /
              (Fintype.card (V n) : ℝ))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C (b n))) /
                (Fintype.card (V n) : ℝ))
      atTop (nhds 0) := by
  classical
  let τ : (n : ℕ) → (C : Finset (V n)) →
      ι → Equiv.Perm {x : V n // x ∈ C} :=
    fun n C i =>
      Classical.choose
        (SoficGroups.exists_completion_of_internal_permutation
          (σ n i) C)
  have hτ (n : ℕ) (C : Finset (V n)) (_hC : C ∈ (P n).parts)
      (i : ι) (x : V n) (hx : x ∈ C) (hy : σ n i x ∈ C) :
      ((τ n C i ⟨x, hx⟩ : {x : V n // x ∈ C}) : V n) =
        σ n i x := by
    exact Classical.choose_spec
      (SoficGroups.exists_completion_of_internal_permutation
        (σ n i) C) x hx hy
  exact weighted_component_midrankVariance_tendsto_zero_of_additive_expansion
    V ι P σ τ b γ hγ hτ hexpand hboundary henergy
end SoficGroups.KunGlobalActualAdditiveMidrankVariance
