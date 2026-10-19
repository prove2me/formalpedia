-- Prove2me | solution 1 for SoficGroups.MatchedComponentExitBudget.sourceCompletionBad_original_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/27f4da23-cd39-4052-96df-36b19a469b34

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_card_sourceCompletionBad_le_deleted_add_wordBad

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators
namespace SoficGroups.MatchedComponentExitBudget
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (B : (n : ℕ) → Finset (V n))
    (hdeleted : Tendsto
      (fun n => ((B n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0))
    (hword : Tendsto
      (fun n =>
        ((sourceWordTestBad (σ n) (p n) F).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((SoficGroups.MatchedComponentCompletion.sourceCompletionBad
          (σ n) (p n) F (Finset.univ \ B n)).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
  let c : ℝ :=
    (Fintype.card ι +
      (SoficGroups.CompressionCriterion.productTrackedTable F).card +
      Fintype.card ι *
        (SoficGroups.CompressionCriterion.productTrackedTable F).card : ℕ)
  have hupper (n : ℕ) :
      ((SoficGroups.MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (Finset.univ \ B n)).card : ℝ) /
          Fintype.card (V n) ≤
        c * (((B n).card : ℝ) / Fintype.card (V n)) +
          ((sourceWordTestBad (σ n) (p n) F).card : ℝ) /
            Fintype.card (V n) := by
    have hfinite := card_sourceCompletionBad_le_deleted_add_wordBad
      (σ n) (p n) F (Finset.univ \ B n)
    have hdeleted_eq :
        (Finset.univ \ (Finset.univ \ B n) : Finset (V n)) = B n := by
      ext x
      simp
    rw [hdeleted_eq] at hfinite
    have hreal :
        ((SoficGroups.MatchedComponentCompletion.sourceCompletionBad
          (σ n) (p n) F (Finset.univ \ B n)).card : ℝ) ≤
            c * ((B n).card : ℝ) +
              (sourceWordTestBad (σ n) (p n) F).card := by
      dsimp [c]
      exact_mod_cast hfinite
    calc
      ((SoficGroups.MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (Finset.univ \ B n)).card : ℝ) /
          Fintype.card (V n) ≤
          (c * ((B n).card : ℝ) +
            (sourceWordTestBad (σ n) (p n) F).card) /
              Fintype.card (V n) :=
            div_le_div_of_nonneg_right hreal (by positivity)
      _ = c * (((B n).card : ℝ) / Fintype.card (V n)) +
          ((sourceWordTestBad (σ n) (p n) F).card : ℝ) /
            Fintype.card (V n) := by
          ring
  have hlimit : Tendsto
      (fun n =>
        c * (((B n).card : ℝ) / Fintype.card (V n)) +
          ((sourceWordTestBad (σ n) (p n) F).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0) := by
    simpa using (hdeleted.const_mul c).add hword
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun n => by positivity)
    (Filter.Eventually.of_forall hupper)
    hlimit
end SoficGroups.MatchedComponentExitBudget
