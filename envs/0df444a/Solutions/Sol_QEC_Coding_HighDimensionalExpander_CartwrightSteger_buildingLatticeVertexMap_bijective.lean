-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:21:48.883569+00:00
-- url     : https://prove2.me/submissions/6a772648-a45d-4e14-a91d-1db39a786dc3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_injective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_surjective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Function.Bijective (buildingLatticeVertexMap P r) :=
  ⟨buildingLatticeVertexMap_injective P r,
    buildingLatticeVertexMap_surjective P r⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
