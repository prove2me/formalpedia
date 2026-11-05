-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixPhases.LoopPlan.run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:24.128553+00:00
-- url     : https://prove2.me/submissions/81827136-5485-4490-9579-f65c61aa31f3

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixPhases
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixPhases_loop_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixLoop_loop_meets


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixPhases
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixLoop
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [instance] Phase.prime
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixPhases
namespace LoopPlan
theorem _root_.solution {lim : Limits} {rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
    depth K R S T : ℕ} {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ} {μ : ℕ→ℤ}
    (H : LoopPlan lim rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
      depth K R S T raws words maps xl yl zl xr yr zr μ) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) 193 depth
      (args rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale)
      μ (LightWeightedGlobalPrefixLoop.time rounds T) (fun z ν=>z=((p^rounds:ℕ):ℤ) ∧ H.invariant rounds ν) :=
  loop_meets μ H.invariant H.initial H.roundsWord H.depthBound H.powerWords H.inputs H.arguments H.powers
    H.stages H.costs H.transition
end LoopPlan
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixPhases
