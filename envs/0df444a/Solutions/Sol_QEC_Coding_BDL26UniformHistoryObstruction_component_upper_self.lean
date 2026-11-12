-- Prove2me | solution 1 for QEC.Coding.BDL26UniformHistoryObstruction.component_upper_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:21:19.656184+00:00
-- url     : https://prove2.me/submissions/dd64bd03-228a-4498-971b-554bc2e40a25

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_component_singleton

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformHistoryObstruction
theorem _root_.solution (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j))
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) : p ∈ upperRegion S j (component S j lower p hp) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [component_singleton]
  exact Finset.mem_singleton_self _
end QEC.Coding.BDL26UniformHistoryObstruction
