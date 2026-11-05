-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredTerminalReceipt.native_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:07:38.539873+00:00
-- url     : https://prove2.me/submissions/333a9796-234a-43dc-a150-281a1356255e

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceControlBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFixedParameters_pairFactor_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedSigned_native_signed_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredLoopSetup_budgets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalConcreteProfile_Profile_F_gt_one


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalArenaSelectedSigned
open WeightedGlobalColoredLoopSetup LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredTerminalReceipt
theorem _root_.solution (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    WeightedGlobalNativeTensorScore.pairedPotential
      (WeightedGlobalArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
        (nativeInput P n free menu c A B C initial)) P.K (J P n)
      (WeightedGlobalArenaSelectedSigned.left (n^κ) P.radix (J P n) (fun i=>B.getD i 0))
      (WeightedGlobalArenaSelectedSigned.right (n^κ) P.radix (J P n) (fun i=>C.getD i 0))=0 := by
  let S:=setup P n free menu c A B C initial
  have hb := budgets P n free menu c A B C initial hmeta hinputs (rounds P n) le_rfl
  have hfac : 0<9*WeightedGlobalArenaBudgetExistence.pairFactor P.m P.F P.K :=
    WeightedGlobalArenaFixedParameters.pairFactor_pos (by have := P.F_gt_one;omega)
  exact WeightedGlobalArenaSelectedSigned.native_signed_zero P.maps P.threshold P.cap P.output
    (input P n free A B C) (arrays P n free menu A B C) P.K n (initialBudget P n A)
    (rounds P n) (n^κ) P.radix A.length P.M
    ((WeightedGlobalArenaFixedParameters.determinantBound P.K P.radix)^8)
    (S.state (rounds P n)) (fun i=>A.getD i 0) (fun i=>B.getD i 0) (fun i=>C.getD i 0)
    hb hfac P.driftBound hinputs.2.2.2.1 (hinputs.2.2.2.2.2.2 A.length hmeta.lengthA) hinputs.2.2.2.2.2.1
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredTerminalReceipt
