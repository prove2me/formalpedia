-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredRuntimeCertificate.body_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T04:07:47.077702+00:00
-- url     : https://prove2.me/submissions/eb4ad170-f1cc-48e3-9dcb-a6ab7ca3e390

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredTerminalReceipt
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinalReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixRuntimeIdentity
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Definitions.Def_Submission_Weighted_Global_TernaryColoredQueryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeCertificate
import Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeCertificate_time_le
import Theorems.Thm_Light_Compiler_Holds_output
import Theorems.Thm_ThreeSum_ColorBandBounds_time_le
import Theorems.Thm_ThreeSum_EncodedColorSourcesCosts_time_le
import Theorems.Thm_ThreeSum_EncodedColorStageCosts_time_le
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_time_le
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le
import Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_time_le
import Theorems.Thm_ThreeSum_SourceFiniteCosts_time_le
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_selected
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected
import Theorems.Thm_ThreeSum_WeightedGlobalColoredPrefixRuntimeIdentity_init_time
import Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeBounds_selected


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredRuntimeCertificate
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalColoredTerminalReceipt WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
namespace ThreeSum.WeightedGlobalColoredRuntimeCertificate
theorem _root_.solution (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    let S:=WeightedGlobalColoredLoopSetup.setup P n free menu c A B C initial
    LightWeightedGlobalColorPreparationProof.time n (J P n) (n^κ)+
      LightWeightedGlobalArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+S.initTime+
      LightWeightedGlobalPreparedPostSelection.time
        (WeightedGlobalArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
          (WeightedGlobalColoredFinalReady.selected P n free menu c A B C initial)) P.H
        (WeightedGlobalColoredFinalReady.cleanup P n free A B C)
        (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial)+10000≤P.colorTime n := by
  intro S
  have hh:=time_le P n free menu c A B C initial hmeta hinputs
  have hi : S.initTime=WeightedGlobalActualSeedRuntime.allPrefixTime (k:=P.k) P.maps P.output
      (state P n free menu c A B C initial).phase (state P n free menu c A B C initial).arena
      (state P n free menu c A B C initial).seeds n :=
    WeightedGlobalColoredPrefixRuntimeIdentity.init_time P n free menu c A B C initial
      (WeightedGlobalColoredFinalReady.selected P n free menu c A B C initial)
      (WeightedGlobalColoredFinalReady.cleanup P n free A B C)
      (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial)
  unfold WeightedGlobalActualColoredRuntime.time at hh
  rw [←hi] at hh
  change LightWeightedGlobalColorPreparationProof.time n (J P n) (n^κ)+
      LightWeightedGlobalArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+S.initTime+
      (LightWeightedGlobalPreparedPostSelection.time
        (WeightedGlobalArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
          (WeightedGlobalColoredFinalReady.selected P n free menu c A B C initial)) P.H
        (WeightedGlobalColoredFinalReady.cleanup P n free A B C)
        (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial)+673)+10000≤P.colorTime n at hh
  omega
end ThreeSum.WeightedGlobalColoredRuntimeCertificate
