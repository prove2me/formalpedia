-- Prove2me | solution 1 for SoficGroups.KunTransportedAmbientOverlap.dominant_component_loss_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/9ed7c9e4-adf9-41b7-8e94-2aa8210084bb

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_sum_dominant_component_losses_le_partition_boundaries

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
    {ι : Type*} [Fintype ι]
    (P Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hexp : ∀ n C, C ∈ (P n).parts →
      ∀ E : Finset (V n), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary (σ n) E : ℝ))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (htarget : Tendsto
      (fun n =>
        (∑ D ∈ (Q n).parts,
          (SoficGroups.boundary (σ n) D : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n => (1 / gamma) *
        ((∑ C ∈ (P n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            Fintype.card (V n) +
          (∑ D ∈ (Q n).parts,
            (SoficGroups.boundary (σ n) D : ℝ)) /
              Fintype.card (V n)))
      atTop (nhds 0) := by
    simpa only [add_zero, mul_zero] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 / gamma : ℝ))
          atTop (nhds (1 / gamma))).mul (hsource.add htarget))
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hupper
  · apply div_nonneg
    · apply Finset.sum_nonneg
      intro C _
      apply sub_nonneg.mpr
      exact_mod_cast Finset.card_le_card
        (Finset.inter_subset_left :
          C ∩ SoficGroups.maximumOverlapPart (Q n) C ⊆ C)
    · exact Nat.cast_nonneg _
  · have hcard : (0 : ℝ) < Fintype.card (V n) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have hbound :=
      sum_dominant_component_losses_le_partition_boundaries
        (P n) (Q n) (σ n) gamma (hexp n)
    have hdivide :
        (∑ C ∈ (P n).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) ≤
          ((∑ C ∈ (P n).parts,
            (SoficGroups.boundary (σ n) C : ℝ)) +
            (∑ D ∈ (Q n).parts,
              (SoficGroups.boundary (σ n) D : ℝ))) / gamma := by
      apply (le_div_iff₀ hgamma).2
      simpa [mul_comm] using hbound
    calc
      (∑ C ∈ (P n).parts,
        ((C.card : ℝ) -
          ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
            Fintype.card (V n) ≤
        (((∑ C ∈ (P n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) +
          (∑ D ∈ (Q n).parts,
            (SoficGroups.boundary (σ n) D : ℝ))) / gamma) /
              Fintype.card (V n) :=
        div_le_div_of_nonneg_right hdivide hcard.le
      _ = (1 / gamma) *
          ((∑ C ∈ (P n).parts,
            (SoficGroups.boundary (σ n) C : ℝ)) /
              Fintype.card (V n) +
            (∑ D ∈ (Q n).parts,
              (SoficGroups.boundary (σ n) D : ℝ)) /
                Fintype.card (V n)) := by
        ring
end SoficGroups.KunTransportedAmbientOverlap
