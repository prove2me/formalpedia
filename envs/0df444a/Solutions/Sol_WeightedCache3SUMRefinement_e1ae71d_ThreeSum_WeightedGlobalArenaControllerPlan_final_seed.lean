-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaControllerPlan.final_seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:56:21.255361+00:00
-- url     : https://prove2.me/submissions/9d7c737b-e2c8-442d-8c57-defa496c3956

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFullController
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerPlan

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaControllerPlan
open Light LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
open WeightedGlobalArenaControllerCore WeightedGlobalArenaLayout
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F r : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaControllerPlan
theorem _root_.solution {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K R S i : ℕ} {raws : List ℤ} {words maps : List ℕ} {μ ν : ℕ→ℤ}
    (h : Final I D K R S i (addr I.free I.capacity 8) raws words maps μ ν)
    (hc : 106≤I.capacity) {xs : List ℤ} (hlen : xs.length≤I.capacity)
    (hseed : Seg μ (addr I.free I.capacity 3) xs) :
    Seg ν (addr I.free I.capacity 3) xs := by
  obtain ⟨ξ,hrep,hspan⟩ := h
  intro j hj
  have hjC : j < I.capacity := hj.trans_le hlen
  have hlt : addr I.free I.capacity 3+j<addr I.free I.capacity 8 := by
    unfold addr
    omega
  have hp : Protected I (addr I.free I.capacity 3+j) := by
    unfold Protected addr at *
    omega
  rw [hspan.2.2.2 _ (Or.inl hlt),hrep.1 _ hp]
  exact hseed j hj
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaControllerPlan
