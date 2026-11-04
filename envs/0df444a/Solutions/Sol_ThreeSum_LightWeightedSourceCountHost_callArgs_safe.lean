-- Prove2me | solution 1 for ThreeSum.LightWeightedSourceCountHost.callArgs_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:24:42.578498+00:00
-- url     : https://prove2.me/submissions/efdc9e67-8b3b-454c-9717-3e63104cdfb9

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_Weighted_SourceCountHost

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedSourceCountHost
theorem _root_.solution (lim : Limits) (σ : State) (offset count : ℕ) :
    ∀ e∈callArgs offset count, e.Safe lim σ := by
  intro e he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  trivial
end ThreeSum.LightWeightedSourceCountHost
