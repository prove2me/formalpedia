-- Prove2me | solution 1 for SoficGroups.exists_matched_slow_diagonal_word_errors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/2cb3b411-c77b-40af-becf-1a2bbd27c16d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finpartition_dominant_matching_injOn
import Theorems.Thm_SoficGroups_matchedCore_missing_density_tendsto_zero
import Theorems.Thm_SoficGroups_exists_diverging_radius_with_vanishing_diagonal_error
import Theorems.Thm_SoficGroups_partitionWordCrossing_indexed_sum_card_le_target_add_unmatched

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)] {ι : Type*}
    (U : ∀ n, Finset (V n))
    (P Q : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (hmajor : ∀ n C, C ∈ R n →
      (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (𝓝 0))
    (I : ℕ → Finset ι)
    (w : ∀ n, ι → Equiv.Perm (V n))
    (hword : ∀ k, Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (partitionWordCrossing (Q n) (w n i)).card : ℕ) : ℝ) /
          (U n).card)
      atTop (𝓝 0))
    (B : ∀ n, ℕ → Finset (V n))
    (hbad : ∀ k, Tendsto
      (fun n => (((U n ∩ B n k).card : ℝ) / (U n).card))
      atTop (𝓝 0)) :
    ∃ r : ℕ → ℕ,
      Tendsto r atTop atTop ∧
        Tendsto
          (fun n =>
            (((∑ i ∈ I (r n),
                (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) +
              (U n ∩ B n (r n)).card) / (U n).card)
          atTop (𝓝 0) := by
  have hmissing := matchedCore_missing_density_tendsto_zero
    U P R hR D hdiscard hsymm
  have hsource (k : ℕ) : Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) /
          (U n).card)
      atTop (𝓝 0) := by
    have hscaled : Tendsto
        (fun n =>
          ((2 * (I k).card : ℕ) : ℝ) *
            (((U n \ matchedCore (R n) (D n)).card : ℝ) /
              (U n).card))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hmissing :
          Tendsto
            (fun n =>
              ((2 * (I k).card : ℕ) : ℝ) *
                (((U n \ matchedCore (R n) (D n)).card : ℝ) /
                  (U n).card))
            atTop (𝓝 (((2 * (I k).card : ℕ) : ℝ) * 0)))
    have hupper : Tendsto
        (fun n =>
          ((∑ i ∈ I k,
            (partitionWordCrossing (Q n) (w n i)).card : ℕ) : ℝ) /
            (U n).card +
            ((2 * (I k).card : ℕ) : ℝ) *
              (((U n \ matchedCore (R n) (D n)).card : ℝ) /
                (U n).card))
        atTop (𝓝 0) := by
      simpa only [add_zero] using (hword k).add hscaled
    refine squeeze_zero (fun n => by positivity) ?_ hupper
    intro n
    have hcard :
        ((∑ i ∈ I k,
          (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) ≤
          ((∑ i ∈ I k,
            (partitionWordCrossing (Q n) (w n i)).card : ℕ) : ℝ) +
            ((2 * (I k).card : ℕ) : ℝ) *
              ((U n \ matchedCore (R n) (D n)).card : ℝ) := by
      exact_mod_cast
        partitionWordCrossing_indexed_sum_card_le_target_add_unmatched
          (P n) (Q n) (R n) (hR n) (D n) (hD n)
          (finpartition_dominant_matching_injOn
            (P n) (R n) (hR n) (D n) (hmajor n))
          (I k) (w n)
    calc
      ((∑ i ∈ I k,
        (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) /
          (U n).card ≤
        (((∑ i ∈ I k,
          (partitionWordCrossing (Q n) (w n i)).card : ℕ) : ℝ) +
          ((2 * (I k).card : ℕ) : ℝ) *
            ((U n \ matchedCore (R n) (D n)).card : ℝ)) /
              (U n).card :=
        div_le_div_of_nonneg_right hcard (by positivity)
      _ = ((∑ i ∈ I k,
            (partitionWordCrossing (Q n) (w n i)).card : ℕ) : ℝ) /
            (U n).card +
            ((2 * (I k).card : ℕ) : ℝ) *
              (((U n \ matchedCore (R n) (D n)).card : ℝ) /
                (U n).card) := by
        ring
  let e : ℕ → ℕ → ℝ := fun n k =>
    (((∑ i ∈ I k,
        (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) +
      (U n ∩ B n k).card) / (U n).card
  have he_nonneg (n k : ℕ) : 0 ≤ e n k := by
    dsimp [e]
    positivity
  have he (k : ℕ) : Tendsto (fun n => e n k) atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun n =>
          ((∑ i ∈ I k,
            (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) /
              (U n).card +
            ((U n ∩ B n k).card : ℝ) / (U n).card)
        atTop (𝓝 0) := by
      simpa only [add_zero] using (hsource k).add (hbad k)
    convert hsum using 1
    funext n
    dsimp [e]
    ring
  obtain ⟨r, hr, her⟩ :=
    exists_diverging_radius_with_vanishing_diagonal_error e he_nonneg he
  exact ⟨r, hr, her⟩
end SoficGroups
