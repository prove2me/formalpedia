-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:58:08.563187+00:00
-- url     : https://prove2.me/submissions/f90fcb9c-da4b-46a7-b2db-27a603ff0650

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (x : BuildingCompactCyclicSemidirect P r) :
    buildingCompactCyclicSemidirectHom P r x =
      buildingConstantPGLHom P r x.left *
        buildingCyclicGeneratorPGL P r ^ x.right.toAdd :=
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
