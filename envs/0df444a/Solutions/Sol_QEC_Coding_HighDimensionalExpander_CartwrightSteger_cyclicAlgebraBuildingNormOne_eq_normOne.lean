-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraBuildingNormOne_eq_normOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:54:23.682938+00:00
-- url     : https://prove2.me/submissions/f1c4f9ae-88d9-4653-af20-3600daba1550

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraReducedNorm_baseChange_eq_buildingReducedNorm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraBuildingNormOne P r = CyclicAlgebraNormOne P r := by
  apply SetLike.ext
  intro u
  change cyclicAlgebraBuildingReducedNorm P r u = 1 ↔
    cyclicAlgebraReducedNorm P r u = 1
  constructor
  · intro hu
    apply Units.map_injective (functionFieldToBuildingLocalField P).injective
    calc
      Units.map (functionFieldToBuildingLocalField P).toMonoidHom
          (cyclicAlgebraReducedNorm P r u) =
        cyclicAlgebraBuildingReducedNorm P r u :=
          cyclicAlgebraReducedNorm_baseChange_eq_buildingReducedNorm P r u
      _ = 1 := hu
      _ = Units.map (functionFieldToBuildingLocalField P).toMonoidHom 1 :=
        (map_one _).symm
  · intro hu
    calc
      cyclicAlgebraBuildingReducedNorm P r u =
        Units.map (functionFieldToBuildingLocalField P).toMonoidHom
          (cyclicAlgebraReducedNorm P r u) :=
            (cyclicAlgebraReducedNorm_baseChange_eq_buildingReducedNorm P r u).symm
      _ = Units.map (functionFieldToBuildingLocalField P).toMonoidHom 1 :=
        congrArg (Units.map
          (functionFieldToBuildingLocalField P).toMonoidHom) hu
      _ = 1 := map_one _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
