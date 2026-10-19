-- Prove2me | solution 1 for SoficGroups.KunResidualRetainedSelection.matchedRetained_boundary_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/b17adaa4-306d-4dc9-9e3c-8d709c69074e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedRetainedSupport_nonempty
import Theorems.Thm_SoficGroups_matchedRetainedSupport_cover_density_tendsto_one
import Theorems.Thm_SoficGroups_KunRootedWordPower_RootedIndicatorMarkovModel_IsRootedAtRadius_mono

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualRetainedSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff
namespace SoficGroups.KunResidualRetainedSelection
theorem _root_.solution
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hRne : ∀ n, (R n).Nonempty)
    (hdiscard : Tendsto
      (fun n => (((U n \ SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (SoficGroups.boundary (σ n) C : ℝ)) /
          (U n).card) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈ R n, (SoficGroups.boundary (σ n) C : ℝ)) /
          (SoficGroups.matchedRetainedSupport (R n)).card)
      atTop (𝓝 0) := by
  have hcover := SoficGroups.matchedRetainedSupport_cover_density_tendsto_one
    U hU P R hR hdiscard
  have hhalf : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤
        ((SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card :=
    (hcover.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono
      fun _ h => h.le
  have htwice : Tendsto
      (fun n =>
        (2 : ℝ) *
          ((∑ C ∈ (P n).parts,
            (SoficGroups.boundary (σ n) C : ℝ)) / (U n).card))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hboundary :
        Tendsto
          (fun n =>
            (2 : ℝ) *
              ((∑ C ∈ (P n).parts,
                (SoficGroups.boundary (σ n) C : ℝ)) / (U n).card))
          atTop (𝓝 ((2 : ℝ) * 0)))
  refine squeeze_zero'
    (Eventually.of_forall fun n => by positivity) ?_ htwice
  filter_upwards [hhalf] with n hn
  have hucard : (0 : ℝ) < (U n).card := by
    exact_mod_cast (hU n).card_pos
  have hrcard :
      (0 : ℝ) < (SoficGroups.matchedRetainedSupport (R n)).card := by
    exact_mod_cast
      (SoficGroups.matchedRetainedSupport_nonempty
        (P n) (R n) (hR n) (hRne n)).card_pos
  have hmass :
      ((U n).card : ℝ) ≤
        2 * (SoficGroups.matchedRetainedSupport (R n)).card := by
    have h := (le_div_iff₀ hucard).1 hn
    linarith
  have hsum :
      (∑ C ∈ R n, (SoficGroups.boundary (σ n) C : ℝ)) ≤
        ∑ C ∈ (P n).parts, (SoficGroups.boundary (σ n) C : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (hR n)
    intro C _ _
    positivity
  calc
    (∑ C ∈ R n, (SoficGroups.boundary (σ n) C : ℝ)) /
        (SoficGroups.matchedRetainedSupport (R n)).card ≤
      (∑ C ∈ (P n).parts, (SoficGroups.boundary (σ n) C : ℝ)) /
        (SoficGroups.matchedRetainedSupport (R n)).card :=
          div_le_div_of_nonneg_right hsum hrcard.le
    _ ≤ 2 *
      ((∑ C ∈ (P n).parts, (SoficGroups.boundary (σ n) C : ℝ)) /
        (U n).card) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hrcard hucard).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (mul_le_mul_of_nonneg_left hmass
          (Finset.sum_nonneg fun C _ =>
            Nat.cast_nonneg (SoficGroups.boundary (σ n) C)))
end SoficGroups.KunResidualRetainedSelection
