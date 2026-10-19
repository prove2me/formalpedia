-- Prove2me | solution 1 for SoficGroups.matchedRetained_bad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/0a82f1c3-e8b0-4b71-8c63-3f505620e02c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedRetainedSupport_subset
import Theorems.Thm_SoficGroups_matchedRetainedSupport_nonempty
import Theorems.Thm_SoficGroups_matchedRetainedSupport_cover_density_tendsto_one

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hRne : ∀ n, (R n).Nonempty)
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0))
    (B : ∀ n, Finset (V n))
    (hbad : Tendsto
      (fun n => (((U n ∩ B n).card : ℝ) / (U n).card))
      atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (((matchedRetainedSupport (R n) ∩ B n).card : ℝ) /
          (matchedRetainedSupport (R n)).card))
      atTop (𝓝 0) := by
  have hcover := matchedRetainedSupport_cover_density_tendsto_one
    U hU P R hR hdiscard
  have hhalf : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤
        ((matchedRetainedSupport (R n)).card : ℝ) / (U n).card :=
    (hcover.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono
      fun _ h => h.le
  have htwice : Tendsto
      (fun n =>
        (2 : ℝ) * (((U n ∩ B n).card : ℝ) / (U n).card))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hbad :
        Tendsto
          (fun n =>
            (2 : ℝ) * (((U n ∩ B n).card : ℝ) / (U n).card))
          atTop (𝓝 ((2 : ℝ) * 0)))
  refine squeeze_zero'
    (Eventually.of_forall fun n => by positivity) ?_ htwice
  filter_upwards [hhalf] with n hn
  have hucard : (0 : ℝ) < (U n).card := by
    exact_mod_cast (hU n).card_pos
  have hrcard : (0 : ℝ) < (matchedRetainedSupport (R n)).card := by
    exact_mod_cast
      (matchedRetainedSupport_nonempty (P n) (R n) (hR n) (hRne n)).card_pos
  have hmass :
      ((U n).card : ℝ) ≤ 2 * (matchedRetainedSupport (R n)).card := by
    have h := (le_div_iff₀ hucard).1 hn
    linarith
  have hbadcard :
      ((matchedRetainedSupport (R n) ∩ B n).card : ℝ) ≤
        (U n ∩ B n).card := by
    exact_mod_cast Finset.card_le_card
      (Finset.inter_subset_inter_right
        (matchedRetainedSupport_subset (P n) (R n) (hR n)))
  calc
    ((matchedRetainedSupport (R n) ∩ B n).card : ℝ) /
        (matchedRetainedSupport (R n)).card ≤
      ((U n ∩ B n).card : ℝ) / (matchedRetainedSupport (R n)).card :=
        div_le_div_of_nonneg_right hbadcard hrcard.le
    _ ≤ 2 * (((U n ∩ B n).card : ℝ) / (U n).card) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hrcard hucard).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (mul_le_mul_of_nonneg_left hmass
          (Nat.cast_nonneg (α := ℝ) (U n ∩ B n).card))
end SoficGroups
