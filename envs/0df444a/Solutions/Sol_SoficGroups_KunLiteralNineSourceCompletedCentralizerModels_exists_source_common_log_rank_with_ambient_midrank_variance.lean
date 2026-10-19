-- Prove2me | solution 1 for SoficGroups.KunLiteralNineSourceCompletedCentralizerModels.exists_source_common_log_rank_with_ambient_midrank_variance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/547cbbd8-406c-4d2a-ba8a-b0545301e478

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_componentVertexMidrank_nonneg
import Theorems.Thm_SoficGroups_componentVertexMidrank_le_one
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_generator_crossing_density_tendsto_zero
import Theorems.Thm_SoficGroups_SourceCommonComponentRankNoBad_exists_common_positive_component_log_rank_with_vanishing_midrank_energy
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_sum_action_energy_tendsto_zero_of_positive_generator_sum
import Theorems.Thm_SoficGroups_KunGlobalActualAdditiveMidrankVariance_weighted_component_midrankVariance_tendsto_zero_of_source_half_expansion
import Theorems.Thm_SoficGroups_KunLiteralNineSourceCompletedCentralizerModels_sourceAmbientFiniteFamily_crossing_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunLiteralNineSourceCompletedCentralizerModels_sourceAmbientActualInverse_crossing_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralNineSourceCompletedCentralizerModels
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunLiteralNineSourceCompletedCentralizerModels
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (SG : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (QΓ QG : (n : ℕ) →
      Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
    (γG : ℝ)
    (hsymmetricG : ∀ g ∈ SG, g⁻¹ ∈ SG)
    (hgeneratesG : Subgroup.closure
      (SG : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode)) =
          ⊤)
    (hpositive : Subgroup.closure
      (Set.range
        (SoficGroups.KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
          SΓ)) = ⊤)
    (hγG : 0 < γG)
    (hexpandG : ∀ n C, C ∈ (QG n).parts →
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          γG * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SG =>
                (A.model n).action
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.ninePrefixCode)) E : ℝ))
    (hboundaryΓ : Tendsto
      (fun n =>
        (∑ C ∈ (QΓ n).parts,
          (SoficGroups.boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SoficGroups.KunExactActualSourceAmbientGenerators.sourceAlphaInclusion
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode))) C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0))
    (hboundaryG : Tendsto
      (fun n =>
        (∑ C ∈ (QG n).parts,
          (SoficGroups.boundary
            (fun i : ↥SG =>
              (A.model n).action
                (i : SoficGroups.prefixElementaryGroup
                  SoficGroups.ninePrefixCode)) C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0))
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (heta : Tendsto eta atTop (𝓝 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (𝓝 0))
    (hoverlap : ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition
            (QΓ n)
            ((A.model n).action
              (SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionTable
                j)))
          (QΓ n) (eta n), (C.card : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0))
    (hloss : ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈
          (SoficGroups.transportedUnivFinpartition
            (QΓ n)
            ((A.model n).action
              (SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionTable
                j))).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (QΓ n) C).card : ℝ))) /
              (A.model n).size)
      atTop (𝓝 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QG n).parts,
            (C.card : ℝ) *
              SoficGroups.midrankVariance
                (SoficGroups.componentRankMassList C
                  (SoficGroups.SourceCommonOffsetMidrankEnergy.componentLogRank
                    (QΓ n) (H n) (r n)))) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      (∀ j : Fin 2, Tendsto
        (fun n =>
          ((SoficGroups.partitionWordCrossing (QG n)
            (((A.model n).action
              (SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionTable
                j))⁻¹)).card : ℝ) /
              (A.model n).size)
        atTop (𝓝 0)) := by
  classical
  letI : ∀ n, Nonempty (Fin (A.model n).size) :=
    fun n => Fin.pos_iff_nonempty.mp (A.model n).size_pos
  let σ : (n : ℕ) → ↥SΓ → Equiv.Perm (Fin (A.model n).size) :=
    fun n i =>
      (A.model n).action
        (SoficGroups.KunExactActualSourceAmbientGenerators.sourceAlphaInclusion
          (i : SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode))
  let T : (n : ℕ) → Fin 2 → Equiv.Perm (Fin (A.model n).size) :=
    fun n j =>
      (A.model n).action
        (SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionTable
          j)
  have hcrossΓ : ∀ i : ↥SΓ, Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (QΓ n)
          (σ n i)).card : ℝ) /
            Fintype.card (Fin (A.model n).size))
      atTop (𝓝 0) := by
    intro i
    exact
      SoficGroups.SourceGeneratedWordCrossing.generator_crossing_density_tendsto_zero
        QΓ σ
        (by simpa only [σ, Fintype.card_fin] using hboundaryΓ)
        i
  have haction (n : ℕ) (i : ↥SΓ ⊕ Fin 2) :
      (A.model n).action
        (SoficGroups.KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
          SΓ i) =
        Sum.elim (σ n) (T n) i := by
    cases i <;> rfl
  have hcrossG : Tendsto
      (fun n =>
        (∑ i : ↥SΓ ⊕ Fin 2,
          ((SoficGroups.partitionWordCrossing
            (QG n) (Sum.elim (σ n) (T n) i)).card : ℝ)) /
              Fintype.card (Fin (A.model n).size))
      atTop (𝓝 0) := by
    simpa only [haction, Fintype.card_fin]
      using sourceAmbientFiniteFamily_crossing_density_tendsto_zero
        A SG hsymmetricG hgeneratesG QG hboundaryG
        (↥SΓ ⊕ Fin 2)
        (SoficGroups.KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
          SΓ)
  obtain ⟨r, hr, _hdrop, hmidpoint⟩ :=
    SoficGroups.SourceCommonComponentRankNoBad.exists_common_positive_component_log_rank_with_vanishing_midrank_energy
      (fun n => Fin (A.model n).size)
      (↥SΓ) (Fin 2) QΓ QG σ T eta H
      heta0 heta1 hH heta hratio hcrossΓ
      (by simpa only [T, Fintype.card_fin] using hoverlap)
      (by simpa only [T, Fintype.card_fin] using hloss)
      hcrossG
  let b : (n : ℕ) → Fin (A.model n).size → ℤ :=
    fun n =>
      SoficGroups.SourceCommonOffsetMidrankEnergy.componentLogRank
        (QΓ n) (H n) (r n)
  let f : (n : ℕ) → Fin (A.model n).size → ℝ :=
    fun n =>
      SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank
        (QG n) (b n)
  have hf0 : ∀ n x, 0 ≤ f n x := by
    intro n x
    exact SoficGroups.componentVertexMidrank_nonneg
      ((QG n).part x) (b n) x
  have hf1 : ∀ n x, f n x ≤ 1 := by
    intro n x
    exact SoficGroups.componentVertexMidrank_le_one
      ((QG n).part x) (b n) x
  have hmidpoint' : Tendsto
      (fun n =>
        (∑ i : ↥SΓ ⊕ Fin 2,
          ∑ x : Fin (A.model n).size,
            (f n (Sum.elim (σ n) (T n) i x) - f n x) ^ 2) /
              (A.model n).size)
      atTop (𝓝 0) := by
    simpa only [f, b, Fintype.card_fin] using hmidpoint
  have hpositiveEnergy : Tendsto
      (fun n =>
        (∑ i : ↥SΓ ⊕ Fin 2,
          SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy
            (f n)
            ((A.model n).action
              (SoficGroups.KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
                SΓ i))) /
              (A.model n).size)
      atTop (𝓝 0) := by
    have hpoint (n : ℕ) (i : ↥SΓ ⊕ Fin 2) :
        SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy
          (f n)
          ((A.model n).action
            (SoficGroups.KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
              SΓ i)) =
          ∑ x : Fin (A.model n).size,
            (f n (Sum.elim (σ n) (T n) i x) - f n x) ^ 2 := by
      rw [haction n i]
      rfl
    simpa only [hpoint] using hmidpoint'
  have hgenerators :=
    SoficGroups.KunPositiveWordMidrankEnergy.sum_action_energy_tendsto_zero_of_positive_generator_sum
      A
      (SoficGroups.KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
        SΓ)
      hpositive f hf0 hf1 hpositiveEnergy SG
  have hgeneratorSum (n : ℕ) :
      (∑ g ∈ SG,
        SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy
          (f n) ((A.model n).action g)) =
      ∑ i : ↥SG,
        SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy
          (f n)
          ((A.model n).action
            (i : SoficGroups.prefixElementaryGroup
              SoficGroups.ninePrefixCode)) := by
    rw [← Finset.sum_coe_sort SG]
  have hsubtypeEnergy : Tendsto
      (fun n =>
        (∑ i : ↥SG,
          SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy
            (f n)
            ((A.model n).action
              (i : SoficGroups.prefixElementaryGroup
                SoficGroups.ninePrefixCode))) /
                (A.model n).size)
      atTop (𝓝 0) := by
    simpa only [hgeneratorSum] using hgenerators
  have hgeneratorEnergy : Tendsto
      (fun n =>
        (∑ i : ↥SG, ∑ x : Fin (A.model n).size,
          (f n ((A.model n).action
            (i : SoficGroups.prefixElementaryGroup
              SoficGroups.ninePrefixCode) x) - f n x) ^ 2) /
            Fintype.card (Fin (A.model n).size))
      atTop (𝓝 0) := by
    simpa only [Fintype.card_fin,
      SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy]
      using hsubtypeEnergy
  have hvariance :=
    SoficGroups.KunGlobalActualAdditiveMidrankVariance.weighted_component_midrankVariance_tendsto_zero_of_source_half_expansion
      (fun n => Fin (A.model n).size) (↥SG) QG
      (fun n i =>
        (A.model n).action
          (i : SoficGroups.prefixElementaryGroup
            SoficGroups.ninePrefixCode))
      b γG hγG hexpandG
      (by simpa only [Fintype.card_fin] using hboundaryG)
      (by simpa only [f] using hgeneratorEnergy)
  refine ⟨r, hr, ?_, ?_⟩
  · simpa only [b, Fintype.card_fin] using hvariance
  · intro j
    exact sourceAmbientActualInverse_crossing_density_tendsto_zero
      A SG hsymmetricG hgeneratesG QG hboundaryG
      (SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionTable
        j)
end SoficGroups.KunLiteralNineSourceCompletedCentralizerModels
