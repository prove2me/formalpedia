-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredTerminalReceipt.collision_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:57:00.955444+00:00
-- url     : https://prove2.me/submissions/70474f4f-b93e-4833-af39-fa2605b36023

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected
import Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopSetup_budgets


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalArenaSelectedSigned
open WeightedGlobalColoredLoopSetup LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
namespace ThreeSum.WeightedGlobalColoredTerminalReceipt
theorem _root_.solution (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    ((TernaryOriginalCollisions.collisionPairs (fun i : Fin B.length=>
      keysB P n free menu c A B C initial i.val)).card : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) ∧
    ((TernaryOriginalCollisions.collisionPairs (fun i : Fin C.length=>
      keysC P n free menu c A B C initial i.val)).card : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) := by
  let S:=setup P n free menu c A B C initial
  have hb:=budgets P n free menu c A B C initial hmeta hinputs (rounds P n) le_rfl
  exact WeightedGlobalArenaSelectedCollisions.selected P.maps P.threshold P.cap P.output
    (input P n free A B C) (arrays P n free menu A B C) A.length (n^κ) P.radix (initialBudget P n A)
    (S.state (rounds P n)) (fun i=>A.getD i 0) (fun i=>B.getD i 0) (fun i=>C.getD i 0)
    P.blockPositive hinputs.1 P.primeLarge P.collisionRate hb
end ThreeSum.WeightedGlobalColoredTerminalReceipt
