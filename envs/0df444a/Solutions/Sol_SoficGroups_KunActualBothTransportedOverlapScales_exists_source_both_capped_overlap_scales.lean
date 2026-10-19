-- Prove2me | solution 1 for SoficGroups.KunActualBothTransportedOverlapScales.exists_source_both_capped_overlap_scales
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/9da459bc-3dc5-4b1b-b0a8-bc7e4b46bd23

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualBothTransportedOverlapScales_exists_source_both_common_slow_overlap_scales

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
      (∀ n, eta n < 1) ∧
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
      ∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈
            (SoficGroups.transportedUnivFinpartition
              (Q n)
              ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))).parts,
            ((C.card : ℝ) -
              ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
                (A.model n).size)
        atTop (nhds 0) := by
  classical
  obtain ⟨eta, H, heta, hetaanti, heta0, hH, hHanti,
    hH0, hratio, hoverlap, hloss, _htail⟩ :=
    exists_source_both_common_slow_overlap_scales
      A S hsymmetric hgenerates Q gamma hgamma hexpand hsource
  let capped : ℕ → ℝ := fun n => min (eta n) ((1 : ℝ) / 2)
  have heventually : ∀ᶠ n in atTop, eta n < (1 : ℝ) / 2 :=
    heta0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have heq : capped =ᶠ[atTop] eta := by
    filter_upwards [heventually] with n hn
    exact min_eq_left hn.le
  have hcappedpositive (n : ℕ) : 0 < capped n := by
    exact lt_min (heta n) (by norm_num : (0 : ℝ) < 1 / 2)
  have hcappedone (n : ℕ) : capped n < 1 := by
    have hhalf : capped n ≤ (1 : ℝ) / 2 :=
      min_le_right _ _
    linarith
  have hcappedanti : Antitone capped := by
    intro m n hmn
    exact min_le_min (hetaanti hmn) (le_refl ((1 : ℝ) / 2))
  have hcappedzero : Tendsto capped atTop (nhds 0) :=
    heta0.congr' heq.symm
  have hcappedratio : Tendsto
      (fun n => capped n / H n) atTop (nhds 0) := by
    have heqratio :
        (fun n => capped n / H n) =ᶠ[atTop]
          (fun n => eta n / H n) := by
      filter_upwards [heq] with n hn
      rw [hn]
    exact hratio.congr' heqratio.symm
  refine ⟨capped, H, hcappedpositive, hcappedone, hcappedanti,
    hcappedzero, hH, hHanti, hH0, hcappedratio, ?_, hloss⟩
  intro j
  have heqoverlap :
      (fun n =>
        (∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition
            (Q n)
            ((A.model n).action
              (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j)))
          (Q n) (capped n), (C.card : ℝ)) /
            (A.model n).size) =ᶠ[atTop]
      (fun n =>
        (∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition
            (Q n)
            ((A.model n).action
              (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j)))
          (Q n) (eta n), (C.card : ℝ)) /
            (A.model n).size) := by
    filter_upwards [heq] with n hn
    rw [hn]
  exact (hoverlap j).congr' heqoverlap.symm
end SoficGroups.KunActualBothTransportedOverlapScales
