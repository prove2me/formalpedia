-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaGuardTransport.primitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:26:41.033986+00:00
-- url     : https://prove2.me/submissions/a01a6b14-fe39-44f3-83d2-1a7bbbc00423

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCandidateGuard
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaScoreScan
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaGuardTransport
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed

namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaGuardTransport
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
private theorem low {I : Input} {x : ℕ} (hx : x<I.free) : Protected I x := by
  unfold Protected addr
  omega
private theorem middle {I : Input} {x : ℕ} (hC : 106≤I.capacity)
    (hl : addr I.free I.capacity 2≤x) (hu : x<addr I.free I.capacity 9) : Protected I x := by
  unfold Protected addr at *
  omega
end ThreeSum.WeightedGlobalArenaGuardTransport
end
end WeightedCache3SUMRefinement_e1ae71d
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaGuardTransport
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaGuardTransport
theorem _root_.solution {I : Input} {A : Inputs} {seed positionCap : ℕ}
    {D : Data (config p r I A seed)} {μ ν : ℕ→ℤ}
    (M : WeightedGlobalArenaSeedPrimitiveGuards.Reads I A seed D μ positionCap)
    (h : KeepInputs I μ ν) (hC : 106≤I.capacity)
    (hnB : I.nB≤I.capacity) (hnC : I.nC≤I.capacity)
    (hnO : I.requesterCount≤I.capacity) (hspan : A.J*p^(r-1)≤I.capacity) :
    WeightedGlobalArenaSeedPrimitiveGuards.Reads I A seed D ν positionCap := by
  have hk : Kept μ ν I.free := fun x hx => h x (low hx)
  refine {M with BRead:=?_,CRead:=?_,ORead:=?_,coeffRead:=?_,oldBRead:=?_,oldCRead:=?_,oldORead:=?_,catalogRead:=?_,positionRead:=?_}
  · intro i hi k hk'
    rw [hk _ (by have := M.matrixB; nlinarith)]
    exact M.BRead i hi k hk'
  · intro i hi k hk'
    rw [hk _ (by have := M.matrixC; nlinarith)]
    exact M.CRead i hi k hk'
  · intro i hi k hk'
    rw [hk _ (by have := M.matrixO; nlinarith)]
    exact M.ORead i hi k hk'
  · intro k hk'
    rw [hk _ (by have := M.menu; omega)]
    exact M.coeffRead k hk'
  · intro i hi
    have he : addr I.free I.capacity 4+I.nB≤addr I.free I.capacity 9 := before (by decide) hnB
    rw [h _ (middle hC (by unfold addr; omega) (by omega))]
    exact M.oldBRead i hi
  · intro i hi
    have he : addr I.free I.capacity 5+I.nC≤addr I.free I.capacity 9 := before (by decide) hnC
    rw [h _ (middle hC (by unfold addr; omega) (by omega))]
    exact M.oldCRead i hi
  · intro i hi
    have he : addr I.free I.capacity 6+I.requesterCount≤addr I.free I.capacity 9 := before (by decide) hnO
    rw [h _ (middle hC (by unfold addr; omega) (by omega))]
    exact M.oldORead i hi
  · intro k hk' i hi
    have he : addr I.free I.capacity 7+A.J*p^(r-1)≤addr I.free I.capacity 9 := before (by decide) hspan
    have hmul := Nat.mul_le_mul_left A.J (Nat.succ_le_of_lt hk')
    rw [h _ (middle hC (by unfold addr; omega) (by nlinarith))]
    exact M.catalogRead k hk' i hi
  · intro i hi
    rw [hk _ (by have := M.positions; omega)]
    exact M.positionRead i hi
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaGuardTransport
