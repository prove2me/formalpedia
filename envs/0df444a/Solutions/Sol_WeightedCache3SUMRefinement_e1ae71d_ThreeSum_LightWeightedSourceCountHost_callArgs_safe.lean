-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.callArgs_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:18:10.249223+00:00
-- url     : https://prove2.me/submissions/4318e6d0-75fe-4898-88e3-31148d5be820

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost
theorem _root_.solution (lim : Limits) (σ : State) (offset count : ℕ) :
    ∀ e∈callArgs offset count, e.Safe lim σ := by
  intro e he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  trivial
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost
