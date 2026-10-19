-- Prove2me | solution 1 for SoficGroups.KunUnconditionalActualSourceDecomposition.exists_unconditional_actual_source_dual_finpartition_sequences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/812477c6-c4e4-405c-9903-5612a80b6bee

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunSourceUnconditionalFullDecomposition_exists_source_subgroup_and_ambient_full_finpartition_sequences
import Theorems.Thm_SoficGroups_KunUnconditionalActualSourceGeneratorData_exists_unconditional_actual_source_generator_data

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUnconditionalActualSourceDecomposition
open Filter Topology
open SoficGroups.KunSourceUnconditionalFullDecomposition
open SoficGroups.KunExactActualSourceAmbientGenerators
open SoficGroups.KunUnconditionalActualSourceGeneratorData
namespace SoficGroups.KunUnconditionalActualSourceDecomposition
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup
        SoficGroups.ninePrefixCode)) :
    ∃ (SΓ : Finset
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode))
      (SG : Finset
          (SoficGroups.prefixElementaryGroup
            SoficGroups.ninePrefixCode))
      (QΓ QG : (n : ℕ) →
        Finpartition
          (Finset.univ : Finset (Fin (A.model n).size)))
      (γΓ γG : ℝ),
      SG = sourceAmbientSymmetricGenerators SΓ ∧
      1 ∈ SΓ ∧
      (∀ g ∈ SΓ, g⁻¹ ∈ SΓ) ∧
      Subgroup.closure
        (SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode)) = ⊤ ∧
      1 ∈ SG ∧
      (∀ g ∈ SG, g⁻¹ ∈ SG) ∧
      Subgroup.closure
        (SG : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.ninePrefixCode)) = ⊤ ∧
      Function.Injective sourceAlphaInclusion ∧
      Subgroup.closure
        (Set.range (sourcePositiveGeneratorMap SΓ)) = ⊤ ∧
      0 < γΓ ∧
      0 < γG ∧
      (∀ n, ∀ C ∈ (QΓ n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γΓ * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (sourceAlphaInclusion (i :
                    SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) E : ℝ)) ∧
      (∀ n, ∀ C ∈ (QG n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γG * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SG =>
                (A.model n).action (i :
                  SoficGroups.prefixElementaryGroup
                    SoficGroups.ninePrefixCode)) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QΓ n).parts,
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (sourceAlphaInclusion (i :
                    SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QG n).parts,
            (SoficGroups.boundary
              (fun i : ↥SG =>
                (A.model n).action (i :
                  SoficGroups.prefixElementaryGroup
                    SoficGroups.ninePrefixCode)) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) := by
  classical
  obtain ⟨SΓ, PΓ, PG, honeΓ, hsymmetricΓ, hgeneratesΓ,
    hPΓ, honeG, hsymmetricG, hgeneratesG, hPG,
    hfaithful, hpositive⟩ :=
      exists_unconditional_actual_source_generator_data
  let SG := sourceAmbientSymmetricGenerators SΓ
  have hcoverΓ : PΓ.generators ⊆ SΓ := by
    rw [hPΓ]
  have hcoverG : PG.generators ⊆ SG := by
    dsimp [SG]
    rw [hPG]
  obtain ⟨γΓ, γG, QΓ, QG, hγΓ, hγG, hexpΓ,
    hexpG, hboundaryΓ, hboundaryG⟩ :=
      exists_source_subgroup_and_ambient_full_finpartition_sequences
        A sourceAlphaInclusion hfaithful
        PΓ PG SΓ SG honeΓ honeG hcoverΓ hcoverG
        hsymmetricΓ hsymmetricG hgeneratesΓ hgeneratesG
  exact ⟨SΓ, SG, QΓ, QG, γΓ, γG, rfl,
    honeΓ, hsymmetricΓ, hgeneratesΓ,
    honeG, hsymmetricG, hgeneratesG, hfaithful,
    hpositive, hγΓ, hγG, hexpΓ, hexpG,
    hboundaryΓ, hboundaryG⟩
end SoficGroups.KunUnconditionalActualSourceDecomposition
