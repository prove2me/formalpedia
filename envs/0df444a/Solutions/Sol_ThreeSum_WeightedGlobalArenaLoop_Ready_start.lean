-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaLoop.Ready.start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:23:29.693981+00:00
-- url     : https://prove2.me/submissions/f250428f-5727-4d2e-9bc3-e7a6c6466f2e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoop
import Theorems.Thm_ThreeSum_LightBalancedOffset_offset_lt
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_lt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaHeaderAgreement_templateValues_length
import Theorems.Thm_ThreeSum_WeightedGlobalArenaLayout_offset_lt
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_template
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_Memory_rebase
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_start_initialized
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaLoop
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixInputs
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
namespace ThreeSum.WeightedGlobalArenaLoop
namespace Ready
theorem _root_.solution {S : Setup p m F K N E} {lim : Limits} {depth : ℕ}
    (H : Ready S lim depth) {μ ν : ℕ→ℤ}
    (hinit : LightWeightedGlobalPrefixInit.Initialized (config p 0 S.input S.arrays 0)
      (addr S.input.free S.input.capacity 3) (S.seedHeader 0) μ ν)
    (hkeep : Kept S.initial μ S.input.free)
    (hTemplate : Seg μ (addr S.input.free S.input.capacity 0)
      (WeightedGlobalArenaHeaderAgreement.templateValues S.input p m F)) : Invariant S 0 ν :=by
  have hc:=H.capacities 0 H.roundsPositive
  have HM:=WeightedGlobalArenaPrefixState.start_initialized (p:=p) S.input S.arrays (fun i t=>S.L i t.val)
    (fun i t=>S.R i t.val) (fun i t=>S.O i t.val) (S.seedHeader 0) μ ν hinit
  have template : Seg ν (addr S.input.free S.input.capacity 0)
      (WeightedGlobalArenaHeaderAgreement.templateValues S.input p m F):=by
    intro i hi
    have hx : addr S.input.free S.input.capacity 0+i<addr S.input.free S.input.capacity 1:=by
      apply offset_lt hi
      rw [WeightedGlobalArenaHeaderAgreement.templateValues_length]
      exact hc.1
    rw [hinit.2.2.2.2.2 _ (Or.inl (by unfold addr at *;omega))
      (Or.inl (by change addr S.input.free S.input.capacity 0+i<addr S.input.free S.input.capacity 4;unfold addr at *;omega))
      (Or.inl (by change addr S.input.free S.input.capacity 0+i<addr S.input.free S.input.capacity 7;unfold addr at *;omega))]
    exact hTemplate i hi
  exact ⟨(fun _ _=>0),HM.rebase hkeep,hinit.1,template,trivial⟩
end Ready
end ThreeSum.WeightedGlobalArenaLoop
