-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredLoopCall.lifted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:51:30.537904+00:00
-- url     : https://prove2.me/submissions/74973165-70ca-471c-9689-2c4eca1dc4ec

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSeedABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopABI
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopReady
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocationScalars
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopCall
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_reporting
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLoop_Ready_init_meets
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalColoredPrefixCall_lift
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopCall
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open LightWeightedGlobalColoredInitializationProof
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ → ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
namespace ThreeSum.WeightedGlobalColoredLoopCall
theorem _root_.solution {lim : Limits} {d : ℕ} (μ : ℕ → ℤ)
    (HR : WeightedGlobalArenaLoop.Ready (setup P n free menu c A B C initial) lim (d + 2))
    (hk : Kept initial μ (input P n free A B C).free)
    (ht :
      Seg μ (addr (input P n free A B C).free (cells P n) 0)
        (WeightedGlobalArenaHeaderAgreement.templateValues (input P n free A B C) P.p P.m P.F))
    (hs : Seg μ (addr (input P n free A B C).free (cells P n) 2) ((setup P n free menu c A B C initial).seedHeader 0)) :
    let S := setup P n free menu c A B C initial
    Meets lim P.color 249 (d + 1) S.initArgs μ S.initTime
      (fun z ν => z = ((P.p ^ (rounds P n) : ℕ) : ℤ) ∧ WeightedGlobalArenaLoop.Invariant S S.rounds ν) :=
  by
  let S := setup P n free menu c A B C initial
  have hm := HR.init_meets μ hk ht hs
  have hh :=
    WeightedGlobalColoredPrefixCall.lift (radix := P.radix) (D := P.allocation.D) (E := P.allocation.E) (K := P.K)
      (bDigit := P.radix) (a := P.p ^ (2 * P.K)) (b := P.drift) (scaleBase := P.scale) (p := P.p) (R :=
      4 ^ fixedLength P.m) (F := P.F) (m := P.m) (alpha2 := fixedAlpha P.m 2) (alphaRank := alphaRank P.m) (localQ :=
      TernaryCodeSemantics.address P.output.val) (L := fixedLength P.m) S.raws S.words S.mapCodes
      ((WeightedGlobalNativeCompleteFrontend.localRecords P.maps P.cap false).map
        (TernaryCanonicalDictionaries.native false P.maps))
      ((WeightedGlobalNativeCompleteFrontend.localRecords P.maps P.cap false).map TernaryCanonicalDictionaries.wordCode)
      ((WeightedGlobalNativeCompleteFrontend.localRecords P.maps P.cap false).map TernaryCanonicalDictionaries.mapCode)
      ((WeightedGlobalNativeCompleteFrontend.localRecords P.maps P.cap true).map
        (TernaryCanonicalDictionaries.native true P.maps))
      ((WeightedGlobalNativeCompleteFrontend.localRecords P.maps P.cap true).map TernaryCanonicalDictionaries.wordCode)
      ((WeightedGlobalNativeCompleteFrontend.localRecords P.maps P.cap true).map TernaryCanonicalDictionaries.mapCode)
      (WeightedGlobalExecutable.reporting P.maps P.cap P.K) (WeightedGlobalExecutable.reportingMain (p := P.p) P.K) hm
  exact hh
end ThreeSum.WeightedGlobalColoredLoopCall
