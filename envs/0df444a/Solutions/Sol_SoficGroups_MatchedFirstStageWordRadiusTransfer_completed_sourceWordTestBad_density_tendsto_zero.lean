-- Prove2me | solution 1 for SoficGroups.MatchedFirstStageWordRadiusTransfer.completed_sourceWordTestBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/331611fb-192b-47e8-82a1-61317d45f7a0

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedFirstStageWordRadiusTransfer_card_completed_sourceWordTestBad_le_sourceCompletionBad

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedFirstStageWordRadiusTransfer
open Filter Topology
open scoped BigOperators
namespace SoficGroups.MatchedFirstStageWordRadiusTransfer
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (P E : (n : ℕ) → Finset (V n))
    (hcapture : ∀ n,
      SoficGroups.MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (P n) ⊆ P n ∩ E n)
    (hradius : Tendsto
      (fun n => (((P n ∩ E n).card : ℝ) / (P n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((SoficGroups.MatchedComponentExitBudget.sourceWordTestBad
          (fun i => SoficGroups.MatchedComponentCompletion.completedRestriction
            (σ n i) (P n))
          (fun j => SoficGroups.MatchedComponentCompletion.completedRestriction
            (p n j) (P n))
          F).card : ℝ) / (P n).card)
      atTop (nhds 0) := by
  have hupper (n : ℕ) :
      ((SoficGroups.MatchedComponentExitBudget.sourceWordTestBad
        (fun i => SoficGroups.MatchedComponentCompletion.completedRestriction
          (σ n i) (P n))
        (fun j => SoficGroups.MatchedComponentCompletion.completedRestriction
          (p n j) (P n))
        F).card : ℝ) / (P n).card ≤
          (((P n ∩ E n).card : ℝ) / (P n).card) := by
    have hfirst := card_completed_sourceWordTestBad_le_sourceCompletionBad
      (σ n) (p n) F (P n)
    have hsecond := Finset.card_le_card (hcapture n)
    have hcard :
        (SoficGroups.MatchedComponentExitBudget.sourceWordTestBad
          (fun i => SoficGroups.MatchedComponentCompletion.completedRestriction
            (σ n i) (P n))
          (fun j => SoficGroups.MatchedComponentCompletion.completedRestriction
            (p n j) (P n))
          F).card ≤ (P n ∩ E n).card := hfirst.trans hsecond
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hcard
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun n => by positivity)
    (Filter.Eventually.of_forall hupper)
    hradius
end SoficGroups.MatchedFirstStageWordRadiusTransfer
