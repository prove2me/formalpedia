-- Prove2me | solution 1 for SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_subgroup_and_ambient_full_finpartition_sequences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/badb1e85-f83b-4303-b95c-ef710029108d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunSourceUnconditionalFullDecomposition_exists_source_full_finpartition_sequence_of_kazhdan

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSourceUnconditionalFullDecomposition
open Filter Topology
namespace SoficGroups.KunSourceUnconditionalFullDecomposition
theorem _root_.solution
    {G Γ : Type} [Group G] [Group Γ]
    [DecidableEq G] [DecidableEq Γ]
    (A : SoficGroups.SoficApproximation G)
    (f : Γ →* G) (hf : Function.Injective f)
    (PΓ : SoficGroups.KazhdanPair.{0, 0} Γ)
    (PG : SoficGroups.KazhdanPair.{0, 0} G)
    (SΓ : Finset Γ) (SG : Finset G)
    (honeΓ : 1 ∈ SΓ) (honeG : 1 ∈ SG)
    (hcoverΓ : PΓ.generators ⊆ SΓ)
    (hcoverG : PG.generators ⊆ SG)
    (hsymmetricΓ : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hsymmetricG : ∀ g ∈ SG, g⁻¹ ∈ SG)
    (hgeneratesΓ : Subgroup.closure (SΓ : Set Γ) = ⊤)
    (hgeneratesG : Subgroup.closure (SG : Set G) = ⊤) :
    ∃ (γΓ γG : ℝ)
      (QΓ QG : (n : ℕ) →
        Finpartition
          (Finset.univ : Finset (Fin (A.model n).size))),
      0 < γΓ ∧
      0 < γG ∧
      (∀ n, ∀ C ∈ (QΓ n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γΓ * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action (f (i : Γ))) E : ℝ)) ∧
      (∀ n, ∀ C ∈ (QG n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γG * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SG =>
                (A.model n).action (i : G)) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QΓ n).parts,
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action (f (i : Γ))) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QG n).parts,
            (SoficGroups.boundary
              (fun i : ↥SG =>
                (A.model n).action (i : G)) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) := by
  obtain ⟨γΓ, QΓ, hγΓ, hexpΓ, hbudgetΓ⟩ :=
    exists_source_full_finpartition_sequence_of_kazhdan
      (SoficGroups.pullbackSoficApproximation f hf A)
      PΓ SΓ honeΓ hcoverΓ hsymmetricΓ hgeneratesΓ
  obtain ⟨γG, QG, hγG, hexpG, hbudgetG⟩ :=
    exists_source_full_finpartition_sequence_of_kazhdan
      A PG SG honeG hcoverG hsymmetricG hgeneratesG
  refine ⟨γΓ, γG, QΓ, QG, hγΓ, hγG, ?_, hexpG, ?_,
    hbudgetG⟩
  · exact hexpΓ
  · exact hbudgetΓ
end SoficGroups.KunSourceUnconditionalFullDecomposition
