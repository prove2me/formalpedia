-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalMomentSourceProgram.positions_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:47:02.480929+00:00
-- url     : https://prove2.me/submissions/09f87862-36d1-40e0-90c3-9f3cf8d7cf87

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentSourceProgram

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalMomentSourceProgram
open Light TernaryWeightChannels
namespace ThreeSum.LightWeightedGlobalMomentSourceProgram
theorem _root_.solution (arity : ℕ) (h : arity=115) :
    ∀ a∈positions, 9≤a ∧ a<arity := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  have hi' := List.mem_range.mp hi
  omega
end ThreeSum.LightWeightedGlobalMomentSourceProgram
