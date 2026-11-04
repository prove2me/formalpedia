-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaCapacity.exists_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:44:44.962249+00:00
-- url     : https://prove2.me/submissions/8446f7a3-1c3c-438f-b061-ad31c7b37749

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCapacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCapacity_polyBound_le_capacity

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaCapacity
open Light WeightedGlobalArenaLayout
namespace ThreeSum.WeightedGlobalArenaCapacity
theorem _root_.solution {need : ℕ→ℕ→Need} (h : PolyNeed need) :
    ∃ D E : ℕ, ∀ n U,
      (need n U).word≤capacity D E (n+U) ∧
      (need n U).cells≤capacity D E (n+U) ∧
      (need n U).depth≤capacity D E (n+U) := by
  obtain ⟨s,k,h⟩ := h
  refine ⟨2^s,2*k,?_⟩
  intro n U
  have hb := polyBound_le_capacity s k n U
  exact ⟨(h n U).1.trans hb,(h n U).2.1.trans hb,(h n U).2.2.trans hb⟩
end ThreeSum.WeightedGlobalArenaCapacity
