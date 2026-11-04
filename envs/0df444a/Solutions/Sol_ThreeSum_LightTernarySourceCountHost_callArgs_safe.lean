-- Prove2me | solution 1 for ThreeSum.LightTernarySourceCountHost.callArgs_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:19:07.432633+00:00
-- url     : https://prove2.me/submissions/94495e86-3780-4838-a9cb-c53aabf45599

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_LightTernaryCountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_ThreeSum_LightTernarySourceCountHost

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernarySourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace ThreeSum.LightTernarySourceCountHost
theorem _root_.solution (lim : Limits) (σ : State) (offset count : ℕ) :
    ∀ e∈callArgs offset count, e.Safe lim σ := by
  intro e he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  trivial
end ThreeSum.LightTernarySourceCountHost
