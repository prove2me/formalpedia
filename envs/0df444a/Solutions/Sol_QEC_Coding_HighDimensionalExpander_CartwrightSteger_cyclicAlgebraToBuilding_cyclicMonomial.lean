-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraToBuilding_cyclicMonomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:05:03.840986+00:00
-- url     : https://prove2.me/submissions/ceb046a7-678f-41c8-a5f9-ceeb839cfd0d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebraBasis
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (k : ℕ) (hk : k < r.matrixRank) :
    cyclicAlgebraToBuilding P r (cyclicMonomial P r c k) =
      buildingConstantMatrix P r c *
        buildingCyclicGeneratorMatrix P r ^ k :=
  cyclicAlgebraToBuildingLinear_cyclicMonomial P r c k hk
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
