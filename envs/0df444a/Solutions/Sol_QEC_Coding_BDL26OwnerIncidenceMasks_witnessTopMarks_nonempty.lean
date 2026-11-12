-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.witnessTopMarks_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:16:55.351677+00:00
-- url     : https://prove2.me/submissions/4b01f953-cfa0-4cf5-910b-eb812991dd60

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_witnessUpper_nonzero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution : witnessTopMarks.Nonempty := by
  have hn := witnessUpper_nonzero
  obtain ⟨p, hp⟩ : ∃ p, witnessUpper.val p ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  refine ⟨witnessTopOwner p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact Or.inl ⟨p, rfl, hp⟩
end QEC.Coding.BDL26OwnerIncidenceMasks
