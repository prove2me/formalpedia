-- Prove2me | solution 1 for SoficGroups.MatchedFirstStageWordRadiusTransfer.completed_sourceWordTestBad_density_tendsto_zero_of_matchedRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/6b0ba1a4-ef9d-463c-ad1b-6b8b29c82768

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedFirstStageWordRadiusTransfer_completed_sourceWordTestBad_density_tendsto_zero

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
    (hcapture : ∀ n,
      SoficGroups.MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (P n) ⊆
          P n ∩ SoficGroups.matchedRadiusBad
            (Q n) (I (r n)) (w n) (B n (r n)))
    (hradius : Tendsto
      (fun n =>
        (((P n ∩ SoficGroups.matchedRadiusBad
          (Q n) (I (r n)) (w n) (B n (r n))).card : ℝ) / (P n).card))
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
  exact completed_sourceWordTestBad_density_tendsto_zero
    V σ p F P
    (fun n => SoficGroups.matchedRadiusBad
      (Q n) (I (r n)) (w n) (B n (r n)))
    hcapture hradius
end SoficGroups.MatchedFirstStageWordRadiusTransfer
