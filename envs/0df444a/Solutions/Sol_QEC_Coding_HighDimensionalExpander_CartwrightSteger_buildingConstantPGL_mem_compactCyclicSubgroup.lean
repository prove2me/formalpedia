-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingConstantPGL_mem_compactCyclicSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:59:19.336925+00:00
-- url     : https://prove2.me/submissions/e48f61e0-0c61-47ad-99af-0ed86ef86141

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingConstantPGLHom P r u ∈ BuildingCompactCyclicSubgroup P r :=
  Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_range_self u))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
