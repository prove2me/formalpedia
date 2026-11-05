-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan.reads
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:20:18.48717+00:00
-- url     : https://prove2.me/submissions/0f54f9aa-505a-4682-8950-6dab7abf0a0b

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaScoreScan

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
variable {p r : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan
