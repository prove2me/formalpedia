-- Prove2me | solution 1 for SoficGroups.KunGlobalActualAdditiveMidrankVariance.weighted_component_midrankVariance_tendsto_zero_of_additive_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/1939cae3-a84b-426c-9869-3ba0ea75b445

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CheegerPoincare_finiteVariance_nonneg
import Theorems.Thm_SoficGroups_ComponentMidrankVariance_componentVertexMidrank_finiteVariance_eq
import Theorems.Thm_SoficGroups_KunCompletedComponentMidrankVariation_normalized_permutationRealVariation_tendsto_zero_of_energy
import Theorems.Thm_SoficGroups_KunGlobalActualAdditiveMidrankVariance_weighted_component_midrankVariance_additive_bound

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
    (τ : (n : ℕ) → (C : Finset (V n)) →
      ι → Equiv.Perm {x : V n // x ∈ C})
    (b : (n : ℕ) → V n → ℤ)
    (γ : ℝ) (hγ : 0 < γ)
    (hτ : ∀ n C, C ∈ (P n).parts → ∀ i (x : V n)
      (hx : x ∈ C) (_hy : σ n i x ∈ C),
      ((τ n C i ⟨x, hx⟩ : {x : V n // x ∈ C}) : V n) =
        σ n i x)
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
  let f : (n : ℕ) → V n → ℝ :=
    fun n =>
      SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank
        (P n) (b n)
  have hN (n : ℕ) : (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hvariation : Tendsto
      (fun n =>
        SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
          (σ n) (f n) / (Fintype.card (V n) : ℝ))
      atTop (nhds 0) := by
    apply SoficGroups.KunCompletedComponentMidrankVariation.normalized_permutationRealVariation_tendsto_zero_of_energy
      V ι σ f
    exact henergy
  have hnonnegative : ∀ n,
      0 ≤
        (∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C (b n))) /
                (Fintype.card (V n) : ℝ) := by
    intro n
    apply div_nonneg _ (hN n).le
    apply Finset.sum_nonneg
    intro C hC
    apply mul_nonneg (Nat.cast_nonneg _)
    rw [← SoficGroups.ComponentMidrankVariance.componentVertexMidrank_finiteVariance_eq
      C (b n) ((P n).nonempty_of_mem_parts hC)]
    exact SoficGroups.CheegerPoincare.finiteVariance_nonneg _
  have hupper (n : ℕ) :
      (∑ C ∈ (P n).parts,
        (C.card : ℝ) *
          SoficGroups.midrankVariance
            (SoficGroups.componentRankMassList C (b n))) /
              (Fintype.card (V n) : ℝ) ≤
        (SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
          (σ n) (f n) / (Fintype.card (V n) : ℝ) +
          5 * ((∑ C ∈ (P n).parts,
            (SoficGroups.boundary (σ n) C : ℝ)) /
              (Fintype.card (V n) : ℝ))) / (2 * γ) := by
    have hfinite :=
      weighted_component_midrankVariance_additive_bound
        (P n) (σ n) (τ n) γ hγ.le (hτ n)
          (hexpand n) (b n)
    have hfinite' :=
      (div_le_div_iff_of_pos_right (hN n)).2 hfinite
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hγ)).2
    calc
      ((∑ C ∈ (P n).parts,
        (C.card : ℝ) *
          SoficGroups.midrankVariance
            (SoficGroups.componentRankMassList C (b n))) /
              (Fintype.card (V n) : ℝ)) * (2 * γ) =
          (2 * γ *
            (∑ C ∈ (P n).parts,
              (C.card : ℝ) *
                SoficGroups.midrankVariance
                  (SoficGroups.componentRankMassList C (b n)))) /
                    (Fintype.card (V n) : ℝ) := by ring
      _ ≤
          (SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
            (σ n) (f n) +
            5 * (∑ C ∈ (P n).parts,
              (SoficGroups.boundary (σ n) C : ℝ))) /
                (Fintype.card (V n) : ℝ) := hfinite'
      _ =
          SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
            (σ n) (f n) / (Fintype.card (V n) : ℝ) +
            5 * ((∑ C ∈ (P n).parts,
              (SoficGroups.boundary (σ n) C : ℝ)) /
                (Fintype.card (V n) : ℝ)) := by ring
  have hlimit : Tendsto
      (fun n =>
        (SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
          (σ n) (f n) / (Fintype.card (V n) : ℝ) +
          5 * ((∑ C ∈ (P n).parts,
            (SoficGroups.boundary (σ n) C : ℝ)) /
              (Fintype.card (V n) : ℝ))) / (2 * γ))
      atTop (nhds 0) := by
    have hsum := hvariation.add (hboundary.const_mul (5 : ℝ))
    have hscaled := hsum.mul_const ((2 * γ)⁻¹)
    simpa only [div_eq_mul_inv, zero_add, zero_mul, mul_zero] using hscaled
  exact squeeze_zero'
    (Eventually.of_forall hnonnegative)
    (Eventually.of_forall hupper)
    hlimit
end SoficGroups.KunGlobalActualAdditiveMidrankVariance
