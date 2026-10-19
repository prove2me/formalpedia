-- Prove2me | solution 1 for SoficGroups.KunActualBothTransportedOverlapScales.source_both_transported_generator_boundary_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/55f7fcc1-cbba-4cd5-821c-4d6b4894ea4a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_conjugated_word_crossing_density_tendsto_zero
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_sum_generator_crossing_eq_sum_partition_boundary
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_source_alpha_word_crossing_density_tendsto_zero
import Theorems.Thm_SoficGroups_SourceBothCompressionNormalization_sourceCompressionTable_conjugates_alpha

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualBothTransportedOverlapScales
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunActualBothTransportedOverlapScales
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥S =>
              (A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode))) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0)) :
    ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥S =>
              (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j) *
                (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                    (i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode)) *
                ((A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)
            C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0) := by
  classical
  have hsource' : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥S =>
              (A.model n).action
                (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode))) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0) := by
    exact hsource
  intro j
  have hcross (i : ↥S) : Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action
              (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j) *
            (A.model n).action
              (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                (i : SoficGroups.prefixElementaryGroup
                  SoficGroups.alphaPrefixCode)) *
            ((A.model n).action
              (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)).card : ℝ) /
              (A.model n).size)
      atTop (nhds 0) := by
    obtain ⟨k, hk⟩ :=
      SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable_conjugates_alpha
        j (i : SoficGroups.prefixElementaryGroup
          SoficGroups.alphaPrefixCode)
    have hword :=
      SoficGroups.SourceGeneratedWordCrossing.source_alpha_word_crossing_density_tendsto_zero
        A S hsymmetric hgenerates Q hsource' k
    have hword' : Tendsto
        (fun n =>
          ((SoficGroups.partitionWordCrossing (Q n)
            ((A.model n).action
              (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j *
                SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode) *
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j)⁻¹))).card : ℝ) /
                (A.model n).size)
        atTop (nhds 0) := by
      rw [hk]
      exact hword
    exact
      SoficGroups.SourceCompressionTransportCrossing.conjugated_word_crossing_density_tendsto_zero
        A
        (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j)
        (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
          (i : SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode))
        Q hword'
  have hsum : Tendsto
      (fun n =>
        ∑ i : ↥S,
          ((SoficGroups.partitionWordCrossing (Q n)
            ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode)) *
              ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)).card : ℝ) /
                (A.model n).size)
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ
      (fun i _ => hcross i)
  have hidentity (n : ℕ) :
      (∑ C ∈ (Q n).parts,
        (SoficGroups.boundary
          (fun i : ↥S =>
            (A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode)) *
              ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)
          C : ℝ)) / (A.model n).size =
        ∑ i : ↥S,
          ((SoficGroups.partitionWordCrossing (Q n)
            ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode)) *
              ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)).card : ℝ) /
                (A.model n).size := by
    have hnat :=
      SoficGroups.SourceGeneratedWordCrossing.sum_generator_crossing_eq_sum_partition_boundary
        (Q n)
        (fun i : ↥S =>
          (A.model n).action
              (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j) *
            (A.model n).action
              (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                (i : SoficGroups.prefixElementaryGroup
                  SoficGroups.alphaPrefixCode)) *
            ((A.model n).action
              (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)
    have hreal :
        (∑ i : ↥S,
          ((SoficGroups.partitionWordCrossing (Q n)
            ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode)) *
              ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)).card : ℝ)) =
          ∑ C ∈ (Q n).parts,
            (SoficGroups.boundary
              (fun i : ↥S =>
                (A.model n).action
                    (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j) *
                  (A.model n).action
                    (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                      (i : SoficGroups.prefixElementaryGroup
                        SoficGroups.alphaPrefixCode)) *
                  ((A.model n).action
                    (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)
              C : ℝ) := by
      exact_mod_cast hnat
    rw [← hreal, Finset.sum_div]
  rw [show
    (fun n =>
      (∑ C ∈ (Q n).parts,
        (SoficGroups.boundary
          (fun i : ↥S =>
            (A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode)) *
              ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)
          C : ℝ)) / (A.model n).size) =
      (fun n =>
        ∑ i : ↥S,
          ((SoficGroups.partitionWordCrossing (Q n)
            ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j) *
              (A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode)) *
              ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))⁻¹)).card : ℝ) /
                (A.model n).size) from funext hidentity]
  exact hsum
end SoficGroups.KunActualBothTransportedOverlapScales
