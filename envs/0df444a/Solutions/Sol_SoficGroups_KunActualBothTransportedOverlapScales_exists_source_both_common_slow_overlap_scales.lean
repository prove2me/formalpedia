-- Prove2me | solution 1 for SoficGroups.KunActualBothTransportedOverlapScales.exists_source_both_common_slow_overlap_scales
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/487dede0-55f7-4a82-8591-fe8f04eb506d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_dominant_component_loss_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_transportedUnivFinpartition_half_expansion
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_transported_partition_boundary_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_exists_common_slow_overlap_scales_for_transported_partitions
import Theorems.Thm_SoficGroups_KunActualBothTransportedOverlapScales_source_both_transported_generator_boundary_density_tendsto_zero

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
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hexpand : ∀ n C, C ∈ (Q n).parts →
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥S =>
                (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                    (i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) E : ℝ))
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
    ∃ eta H : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧
      Antitone eta ∧
      Tendsto eta atTop (nhds 0) ∧
      (∀ n, 0 < H n) ∧
      Antitone H ∧
      Tendsto H atTop (nhds 0) ∧
      Tendsto (fun n => eta n / H n) atTop (nhds 0) ∧
      (∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈ SoficGroups.insufficientOverlapComponents
            (SoficGroups.transportedUnivFinpartition
              (Q n)
              ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j)))
            (Q n) (eta n), (C.card : ℝ)) /
              (A.model n).size)
        atTop (nhds 0)) ∧
      (∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈
            (SoficGroups.transportedUnivFinpartition
              (Q n)
              ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))).parts,
            ((C.card : ℝ) -
              ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
                (A.model n).size)
        atTop (nhds 0)) ∧
      ∃ N : ℕ, ∀ n : ℕ, eta (n + N) < 1 := by
  classical
  have hnonempty (n : ℕ) : Nonempty (Fin (A.model n).size) :=
    Fin.pos_iff_nonempty.mp (A.model n).size_pos
  letI : ∀ n, Nonempty (Fin (A.model n).size) := hnonempty
  let σ : (n : ℕ) → ↥S → Equiv.Perm (Fin (A.model n).size) :=
    fun n i =>
      (A.model n).action
        (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
          (i : SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode))
  let T : (n : ℕ) → Fin 2 → Equiv.Perm (Fin (A.model n).size) :=
    fun n j =>
      (A.model n).action
        (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j)
  have hsource' : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            Fintype.card (Fin (A.model n).size))
      atTop (nhds 0) := by
    simpa only [σ, Fintype.card_fin] using hsource
  have htarget : ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i => T n j * σ n i * (T n j)⁻¹) C : ℝ)) /
              Fintype.card (Fin (A.model n).size))
      atTop (nhds 0) := by
    intro j
    simpa only [σ, T, Fintype.card_fin] using
      source_both_transported_generator_boundary_density_tendsto_zero
        A S hsymmetric hgenerates Q hsource j
  obtain ⟨eta, H, heta, hetaanti, heta0, hH, hHanti,
    hH0, hratio, hoverlap⟩ :=
    SoficGroups.KunTransportedAmbientOverlap.exists_common_slow_overlap_scales_for_transported_partitions
      Q σ T gamma hgamma
      (by
        intro n C hC E hE hhalf
        simpa only [σ] using hexpand n C hC E hE hhalf)
      hsource' htarget
  have hloss : ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈
          (SoficGroups.transportedUnivFinpartition
            (Q n) (T n j)).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (Fin (A.model n).size))
      atTop (nhds 0) := by
    intro j
    apply
      SoficGroups.KunTransportedAmbientOverlap.dominant_component_loss_density_tendsto_zero
        (fun n =>
          SoficGroups.transportedUnivFinpartition (Q n) (T n j))
        Q (fun n i => T n j * σ n i * (T n j)⁻¹)
        gamma hgamma
    · intro n
      exact
        SoficGroups.KunTransportedAmbientOverlap.transportedUnivFinpartition_half_expansion
          (Q n) (σ n) (T n j) gamma
          (fun C hC E hE hhalf =>
            by simpa only [σ] using hexpand n C hC E hE hhalf)
    · exact
        SoficGroups.KunTransportedAmbientOverlap.transported_partition_boundary_density_tendsto_zero
          Q σ (fun n => T n j) hsource'
    · exact htarget j
  have htail : ∃ N : ℕ, ∀ n : ℕ, eta (n + N) < 1 := by
    have heventually : ∀ᶠ n in atTop, eta n < 1 :=
      heta0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    obtain ⟨N, hN⟩ := (eventually_atTop.1 heventually)
    refine ⟨N, ?_⟩
    intro n
    apply hN
    omega
  refine ⟨eta, H, heta, hetaanti, heta0, hH, hHanti,
    hH0, hratio, ?_, ?_, htail⟩
  · intro j
    simpa only [T, Fintype.card_fin] using hoverlap j
  · intro j
    simpa only [T, Fintype.card_fin] using hloss j
end SoficGroups.KunActualBothTransportedOverlapScales
