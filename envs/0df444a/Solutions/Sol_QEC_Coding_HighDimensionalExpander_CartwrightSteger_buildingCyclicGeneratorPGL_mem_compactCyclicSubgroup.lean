-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicGeneratorPGL_mem_compactCyclicSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:58:27.335994+00:00
-- url     : https://prove2.me/submissions/52cc7b3e-54ab-43b2-8a1c-e216cbb9e434

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    buildingCyclicGeneratorPGL P r ∈ BuildingCompactCyclicSubgroup P r :=
  Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton _))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
