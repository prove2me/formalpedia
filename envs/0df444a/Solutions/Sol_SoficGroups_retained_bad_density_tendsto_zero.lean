-- Prove2me | solution 1 for SoficGroups.retained_bad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/57df46ad-d4ad-4958-a9f5-43d670610ddc

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {α : ℕ → Type*} [∀ n, DecidableEq (α n)]
    (V U B : ∀ n, Finset (α n))
    (hV : ∀ n, (V n).Nonempty) (hU : ∀ n, (U n).Nonempty)
    (hUV : ∀ n, U n ⊆ V n)
    (hcover : Tendsto
      (fun n => ((U n).card : ℝ) / (V n).card) atTop (𝓝 1))
    (hbad : Tendsto
      (fun n => (((V n ∩ B n).card : ℝ) / (V n).card))
      atTop (𝓝 0)) :
    Tendsto (fun n => (((U n ∩ B n).card : ℝ) / (U n).card))
      atTop (𝓝 0) := by
  have hhalf : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ ((U n).card : ℝ) / (V n).card :=
    (hcover.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono
      fun _ h => h.le
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (by simpa using (tendsto_const_nhds.mul hbad :
      Tendsto
        (fun n => (2 : ℝ) *
          (((V n ∩ B n).card : ℝ) / (V n).card))
        atTop (𝓝 ((2 : ℝ) * 0))))
  filter_upwards [hhalf] with n hn
  have hv : (0 : ℝ) < (V n).card := by
    exact_mod_cast (hV n).card_pos
  have hu : (0 : ℝ) < (U n).card := by
    exact_mod_cast (hU n).card_pos
  have hmass : ((V n).card : ℝ) ≤ 2 * (U n).card := by
    have h := (le_div_iff₀ hv).1 hn
    linarith
  have hbadcard :
      ((U n ∩ B n).card : ℝ) ≤ (V n ∩ B n).card := by
    exact_mod_cast Finset.card_le_card
      (Finset.inter_subset_inter_right (hUV n) :
        U n ∩ B n ⊆ V n ∩ B n)
  calc
    ((U n ∩ B n).card : ℝ) / (U n).card ≤
        ((V n ∩ B n).card : ℝ) / (U n).card :=
      div_le_div_of_nonneg_right hbadcard hu.le
    _ ≤ 2 * (((V n ∩ B n).card : ℝ) / (V n).card) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hu hv).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (mul_le_mul_of_nonneg_left hmass
          (Nat.cast_nonneg (α := ℝ) (V n ∩ B n).card))
end SoficGroups
