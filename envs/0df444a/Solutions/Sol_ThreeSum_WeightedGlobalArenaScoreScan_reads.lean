-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaScoreScan.reads
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:17:33.669705+00:00
-- url     : https://prove2.me/submissions/b55d3a9c-e697-4bee-89d9-be5558eb546d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
variable {p r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaScoreScan
theorem _root_.solution {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K n U : ℕ} {μ ν : ℕ→ℤ} (h : Invariant I (values D K) μ n ν)
    (hf : ∀i < n, |D.flag i|≤1) (hb : ∀i < n, |D.scoreB i|≤U)
    (hc : ∀i < n, |D.scoreC i|≤U) (hp : ∀i < n, |D.scoreP K i|≤U) :
    (∀i < n, ν ((config p r I A 0).flags+i)=D.flag i ∧ |D.flag i|≤1) ∧
    (∀i < n, ν ((config p r I A 0).scoreB+i)=D.scoreB i ∧ |D.scoreB i|≤U) ∧
    (∀i < n, ν ((config p r I A 0).scoreC+i)=D.scoreC i ∧ |D.scoreC i|≤U) ∧
    (∀i < n, ν ((config p r I A 0).scorePaired+i)=D.scoreP K i ∧ |D.scoreP K i|≤U) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    exact ⟨h.2 i hi 0,hf i hi⟩
  · intro i hi
    exact ⟨h.2 i hi 1,hb i hi⟩
  · intro i hi
    exact ⟨h.2 i hi 2,hc i hi⟩
  · intro i hi
    exact ⟨h.2 i hi 3,hp i hi⟩
end ThreeSum.WeightedGlobalArenaScoreScan
