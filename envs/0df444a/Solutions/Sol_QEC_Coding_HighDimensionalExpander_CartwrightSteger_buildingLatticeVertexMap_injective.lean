-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:18:28.239541+00:00
-- url     : https://prove2.me/submissions/9cfa6959-0aef-4ed5-a330-6fa7bac9b211

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCartwrightStegerLattice_stabilizer_trivial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_injective_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Function.Injective (buildingLatticeVertexMap P r) := by
  rw [buildingLatticeVertexMap_injective_iff]
  exact buildingCartwrightStegerLattice_stabilizer_trivial P r
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
