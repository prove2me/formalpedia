-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCapacity.exists_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:16:14.481202+00:00
-- url     : https://prove2.me/submissions/17d909d3-ef08-4f32-aac9-b4508d187b5d

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCapacity
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaCapacity_polyBound_le_capacity

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCapacity
open Light WeightedGlobalArenaLayout
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCapacity
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCapacity
