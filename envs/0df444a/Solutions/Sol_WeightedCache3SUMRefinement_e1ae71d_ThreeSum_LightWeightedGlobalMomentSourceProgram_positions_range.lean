-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram.positions_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:10:25.012441+00:00
-- url     : https://prove2.me/submissions/7d6cf0ca-127f-488d-85d6-e2a556e3de42

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentSourceProgram

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram
open Light TernaryWeightChannels
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram
theorem _root_.solution (arity : ℕ) (h : arity=115) :
    ∀ a∈positions, 9≤a ∧ a<arity := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  have hi' := List.mem_range.mp hi
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram
