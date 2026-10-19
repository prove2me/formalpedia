-- Prove2me | solution 1 for SoficGroups.matchedCore_missing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/e8097f05-0ddb-4e8a-8c56-d7a666b97c4e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedCore_missing_card_le_symmDiff

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (𝓝 0)) :
    Tendsto
      (fun n => (((U n \ matchedCore (R n) (D n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun n =>
        ((U n \ matchedRetainedSupport (R n)).card : ℝ) / (U n).card +
          ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (𝓝 0) := by
    simpa only [zero_add] using hdiscard.add hsymm
  refine squeeze_zero (fun n => by positivity) ?_ hsum
  intro n
  have hcard :
      ((U n \ matchedCore (R n) (D n)).card : ℝ) ≤
        (U n \ matchedRetainedSupport (R n)).card +
          ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) := by
    exact_mod_cast matchedCore_missing_card_le_symmDiff
      (P n) (R n) (hR n) (D n)
  calc
    ((U n \ matchedCore (R n) (D n)).card : ℝ) / (U n).card ≤
        (((U n \ matchedRetainedSupport (R n)).card : ℝ) +
          ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ)) / (U n).card :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = ((U n \ matchedRetainedSupport (R n)).card : ℝ) / (U n).card +
          ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card := by
      ring
end SoficGroups
