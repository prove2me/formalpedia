-- Prove2me | solution 1 for SoficGroups.KunTransportedAmbientOverlap.exists_common_slow_overlap_scales_for_transported_partitions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/6a795a35-a2cb-4080-88ea-07d513d323d7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_insufficientOverlapComponents_mass_le_loss
import Theorems.Thm_SoficGroups_exists_positive_antitone_slow_overlap_scales
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_dominant_component_loss_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_transportedUnivFinpartition_half_expansion
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_transported_partition_boundary_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunTransportedAmbientOverlap
theorem _root_.solution
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (T : (n : ℕ) → κ → Equiv.Perm (V n))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hexp : ∀ n C, C ∈ (Q n).parts →
      ∀ E : Finset (V n), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary (σ n) E : ℝ))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (htarget : ∀ j : κ, Tendsto
      (fun n =>
        (∑ D ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i => T n j * σ n i * (T n j)⁻¹) D : ℝ)) /
              Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ eta H : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧
        Antitone eta ∧
        Tendsto eta atTop (nhds 0) ∧
        (∀ n, 0 < H n) ∧
        Antitone H ∧
        Tendsto H atTop (nhds 0) ∧
        Tendsto (fun n => eta n / H n) atTop (nhds 0) ∧
        ∀ j : κ, Tendsto
          (fun n =>
            (∑ C ∈ SoficGroups.insufficientOverlapComponents
              (SoficGroups.transportedUnivFinpartition
                (Q n) (T n j))
              (Q n) (eta n), (C.card : ℝ)) /
                Fintype.card (V n))
          atTop (nhds 0) := by
  classical
  let L : κ → ℕ → ℝ := fun j n =>
    (∑ C ∈
      (SoficGroups.transportedUnivFinpartition
        (Q n) (T n j)).parts,
      ((C.card : ℝ) -
        ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
          Fintype.card (V n)
  have hLnonneg (j : κ) (n : ℕ) : 0 ≤ L j n := by
    dsimp [L]
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro C _
      apply sub_nonneg.mpr
      exact_mod_cast Finset.card_le_card
        (Finset.inter_subset_left :
          C ∩ SoficGroups.maximumOverlapPart (Q n) C ⊆ C)
    · exact Nat.cast_nonneg _
  have hLlimit (j : κ) :
      Tendsto (L j) atTop (nhds 0) := by
    apply dominant_component_loss_density_tendsto_zero
      (fun n =>
        SoficGroups.transportedUnivFinpartition (Q n) (T n j))
      Q
      (fun n i => T n j * σ n i * (T n j)⁻¹)
      gamma hgamma
    · intro n
      exact transportedUnivFinpartition_half_expansion
        (Q n) (σ n) (T n j) gamma (hexp n)
    · exact transported_partition_boundary_density_tendsto_zero
        Q σ (fun n => T n j) hsource
    · exact htarget j
  let e : ℕ → ℝ := fun n => ∑ j : κ, L j n
  have henonneg (n : ℕ) : 0 ≤ e n := by
    exact Finset.sum_nonneg fun j _ => hLnonneg j n
  have helimit : Tendsto e atTop (nhds 0) := by
    dsimp [e]
    simpa using
      tendsto_finsetSum Finset.univ
        (fun j _ => hLlimit j)
  obtain ⟨eta, H, heta, hetaanti, hetalimit,
    hH, hHanti, hHlimit, hslow, hratio⟩ :=
    SoficGroups.exists_positive_antitone_slow_overlap_scales
      e henonneg helimit
  refine ⟨eta, H, heta, hetaanti, hetalimit,
    hH, hHanti, hHlimit, hratio, ?_⟩
  intro j
  refine squeeze_zero (fun n =>
    div_nonneg (Finset.sum_nonneg fun C _ => Nat.cast_nonneg C.card)
      (Nat.cast_nonneg _)) ?_ hslow
  intro n
  let P : Finpartition (Finset.univ : Finset (V n)) :=
    SoficGroups.transportedUnivFinpartition (Q n) (T n j)
  have hmass :=
    SoficGroups.insufficientOverlapComponents_mass_le_loss
      P (Q n) (eta n)
  have hdivide :
      (∑ C ∈ SoficGroups.insufficientOverlapComponents
        P (Q n) (eta n), (C.card : ℝ)) ≤
          (∑ C ∈ P.parts,
            ((C.card : ℝ) -
              ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card :
                ℝ))) / eta n := by
    apply (le_div_iff₀ (heta n)).2
    simpa [mul_comm] using hmass
  have hcard : (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hsingle : L j n ≤ e n := by
    exact Finset.single_le_sum
      (fun k _ => hLnonneg k n)
      (Finset.mem_univ j)
  change
    (∑ C ∈ SoficGroups.insufficientOverlapComponents
      P (Q n) (eta n), (C.card : ℝ)) /
        Fintype.card (V n) ≤ e n / eta n
  calc
    (∑ C ∈ SoficGroups.insufficientOverlapComponents
      P (Q n) (eta n), (C.card : ℝ)) /
        Fintype.card (V n) ≤
      ((∑ C ∈ P.parts,
        ((C.card : ℝ) -
          ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
            eta n) / Fintype.card (V n) :=
      div_le_div_of_nonneg_right hdivide hcard.le
    _ = L j n / eta n := by
      dsimp [L, P]
      ring
    _ ≤ e n / eta n :=
      div_le_div_of_nonneg_right hsingle (heta n).le
end SoficGroups.KunTransportedAmbientOverlap
