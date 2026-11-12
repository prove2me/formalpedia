-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_buildingInteger_coordinate_of_cyclicAlgebra_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:49:30.957642+00:00
-- url     : https://prove2.me/submissions/e20f3c0d-e317-42f0-bace-308b20df3171

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticIntersection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_GlobalBuildingLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLocalCyclicBasis_repr_cyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLocalCyclicBasis_repr_integralMatrix

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r x)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ f : BuildingIntegerRing P,
      SphericalHecke.integerEmbedding (BaseField P) f =
        functionFieldToBuildingLocalField P
          ((functionFieldCyclicBasis P r).repr x p) := by
  obtain ⟨M, hM⟩ := hlocal
  refine ⟨(buildingIntegralCyclicBasis P r).repr M p, ?_⟩
  rw [← buildingLocalCyclicBasis_repr_integralMatrix P r M p, hM,
    buildingLocalCyclicBasis_repr_cyclicAlgebra]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
