-- Prove2me | solution 1 for SoficGroups.MatchedFirstStageWordRadiusTransfer.pruned_sourceCompletionBad_density_tendsto_zero_of_matchedRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/5bb87244-a13f-4e6d-9420-596814a2e8b7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_sourceCompletionBad_surviving_density_tendsto_zero
import Theorems.Thm_SoficGroups_MatchedFirstStageWordRadiusTransfer_completed_sourceWordTestBad_density_tendsto_zero_of_matchedRadius

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
    {ι κ J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (U P : (n : ℕ) → Finset (V n))
    (Q : (n : ℕ) → Finpartition (U n))
    (I : ℕ → Finset κ)
    (w : (n : ℕ) → κ → Equiv.Perm (V n))
    (r : ℕ → ℕ)
    (B : (n : ℕ) → ℕ → Finset (V n))
    (D : (n : ℕ) → Finset {x : V n // x ∈ P n})
    (hcapture : ∀ n,
      SoficGroups.MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (P n) ⊆
          P n ∩ SoficGroups.matchedRadiusBad
            (Q n) (I (r n)) (w n) (B n (r n)))
    (hradius : Tendsto
      (fun n =>
        (((P n ∩ SoficGroups.matchedRadiusBad
          (Q n) (I (r n)) (w n) (B n (r n))).card : ℝ) / (P n).card))
      atTop (nhds 0))
    (hZ : ∀ n,
      (Finset.univ \ D n :
        Finset {x : V n // x ∈ P n}).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (P n).card)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((SoficGroups.MatchedComponentCompletion.sourceCompletionBad
          (fun i => SoficGroups.MatchedComponentCompletion.completedRestriction
            (σ n i) (P n))
          (fun j => SoficGroups.MatchedComponentCompletion.completedRestriction
            (p n j) (P n))
          F (Finset.univ \ D n)).card : ℝ) /
          (Finset.univ \ D n :
            Finset {x : V n // x ∈ P n}).card)
      atTop (nhds 0) := by
  have hword :=
    completed_sourceWordTestBad_density_tendsto_zero_of_matchedRadius
      V σ p F U P Q I w r B hcapture hradius
  apply SoficGroups.MatchedComponentExitBudget.sourceCompletionBad_surviving_density_tendsto_zero
      (fun n => {x : V n // x ∈ P n})
      (fun n i =>
        SoficGroups.MatchedComponentCompletion.completedRestriction
          (σ n i) (P n))
      (fun n j =>
        SoficGroups.MatchedComponentCompletion.completedRestriction
          (p n j) (P n))
      F D hZ
  · simpa only [Fintype.card_coe] using hdeleted
  · simpa only [Fintype.card_coe] using hword
end SoficGroups.MatchedFirstStageWordRadiusTransfer
