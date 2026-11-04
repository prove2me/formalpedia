-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaTerminalReceipt.source_input_signed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:37:16.960447+00:00
-- url     : https://prove2.me/submissions/5dac5c39-bf2f-4a84-88be-434a23db3c39

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaTerminalReceipt_source_input_run
import Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_Resources_run
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_left_bound
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_bound
import Theorems.Thm_ThreeSum_LightWeightedGlobalCertifiedMomentDriver_Resources_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixPhases_LoopPlan_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixPhases_Phase_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixStep_PrepareReady_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_input_eq
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_left_bound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_requester_bound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_right_bound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_signed_nonnegative
import Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_left_bound
import Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_right_bound
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalArenaSelectedSigned WeightedGlobalArenaSelectedTerminal WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 7000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace ThreeSum.WeightedGlobalArenaTerminalReceipt
theorem _root_.solution (maps : Fin F→Weight m p) (τ cap U V scoreBound tag : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (j radix K n nA U0 : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p) (X B C : ℕ→ℤ)
    (catalogs : ℕ→ℕ→ℕ→ℕ) (catalog : ℕ→ℕ→ℕ)
    (hb : 1<radix) (hp : radix≤p) (hbase : WeightedGlobalArenaSelectedSigned.base I A.J nA=I) :
    let L := left U radix A.J B
    let R := right U radix A.J C
    let O := requester U radix A.J X
    let s := run maps τ cap U V scoreBound Q I A radix K n U0 e ℓ L R O catalogs j
    let f := WeightedGlobalArenaPhase.family maps τ cap tag Q I A j radix ℓ (seedAt e) L R O s catalog
    let i := f.pick K N (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1))
      (9^(j+1)*n^2) (9^(j+1)*n^2) (U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1))-1
    let s' := run maps τ cap U V scoreBound Q I A radix K n U0 e ℓ L R O catalogs (j+1)
    sourceInput I A i (f.candidate i).data=
      WeightedGlobalArenaNativeComplete.input I U radix nA (selectedHash A s' (j+1)) X B C := by
  intro L R O s f i s'
  have hh := source_input_run maps τ cap U V scoreBound tag Q I A j radix K n U0 e ℓ L R O catalogs catalog
    (fun i t => signed_nonnegative hp (left_bound hb B i t.val))
    (fun i t => signed_nonnegative hp (right_bound hb C i t.val))
    (fun i t => signed_nonnegative hp (requester_bound hb X i t.val))
  have hs := WeightedGlobalArenaSelectedSigned.input_eq I A s' (j+1) U radix nA X B C
  rw [hbase] at hs
  exact hh.trans hs
end ThreeSum.WeightedGlobalArenaTerminalReceipt
