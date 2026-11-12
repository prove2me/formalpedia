-- Prove2me | solution 1 for QEC.Coding.BDL26OwnerIncidenceMasks.componentWithLower_upper_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:31:44.827393+00:00
-- url     : https://prove2.me/submissions/005292e9-9a95-4a79-866a-bdab72f93095

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_componentWithLower_singleton

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26OwnerIncidenceMasks
theorem _root_.solution (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    p ∈ upperOwnerMaskRegion (componentWithLower lower p hp) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [componentWithLower_singleton]
  exact Finset.mem_singleton_self _
end QEC.Coding.BDL26OwnerIncidenceMasks
