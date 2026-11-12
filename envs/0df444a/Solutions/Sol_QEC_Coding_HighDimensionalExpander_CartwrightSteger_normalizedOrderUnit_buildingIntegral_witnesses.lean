-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.normalizedOrderUnit_buildingIntegral_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:57:00.354907+00:00
-- url     : https://prove2.me/submissions/27a6362d-cc1e-432c-9a8e-6dab7e01d0e6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_normalizedOrderUnit_mem_integralGeneralLinearSet
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_powerSeriesGeneralLinearToLocal
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesGeneralLinearToInteger_inverse
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeries_integer_local_triangle


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank)
    (hq : SphericalHecke.localUnitOrder
        (Matrix.GeneralLinearGroup.det
          (cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u))) =
      (r.matrixRank : ℤ) * q) :
    (∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            (normalizedOrderUnit P r u q : CartwrightStegerOrder P r))) ∧
    (∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r
            (((normalizedOrderUnit P r u q)⁻¹ :
              (CartwrightStegerOrder P r)ˣ) :
                CartwrightStegerOrder P r))) := by
  let A := cyclicUnitToBuildingGL P r
    (orderUnitToCyclicUnit P r (normalizedOrderUnit P r u q))
  have hA : A ∈ SphericalHecke.integralGeneralLinearSet
      (BaseField P) r.matrixRank :=
    normalizedOrderUnit_mem_integralGeneralLinearSet
      P r u q hcompact hq
  rw [← SphericalHecke.range_integralGeneralLinearToLocal] at hA
  obtain ⟨D, hD⟩ := hA
  let C := SphericalHecke.integerGeneralLinearToPowerSeries
    (BaseField P) r.matrixRank D
  have hC : SphericalHecke.powerSeriesGeneralLinearToLocal
      (BaseField P) r.matrixRank C = A := by
    rw [← SphericalHecke.powerSeries_integer_local_triangle]
    rw [SphericalHecke.powerSeriesGeneralLinearToInteger_inverse]
    exact hD
  have hCval := congrArg Units.val hC
  have hCinv : SphericalHecke.powerSeriesGeneralLinearToLocal
      (BaseField P) r.matrixRank C⁻¹ = A⁻¹ := by
    rw [map_inv, hC]
  have hCinvVal := congrArg Units.val hCinv
  constructor
  · refine ⟨(C : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P)), ?_⟩
    calc
      _ = (SphericalHecke.powerSeriesGeneralLinearToLocal
          (BaseField P) r.matrixRank C :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (BuildingLocalField P)) :=
        (SphericalHecke.coe_powerSeriesGeneralLinearToLocal C).symm
      _ = (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) := hCval
      _ = _ := rfl
  · refine ⟨((C⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (BuildingIntegerRing P)) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (BuildingIntegerRing P)), ?_⟩
    calc
      _ = (SphericalHecke.powerSeriesGeneralLinearToLocal
          (BaseField P) r.matrixRank C⁻¹ :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (BuildingLocalField P)) :=
        (SphericalHecke.coe_powerSeriesGeneralLinearToLocal C⁻¹).symm
      _ = ((A⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (BuildingLocalField P)) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (BuildingLocalField P)) := hCinvVal
      _ = _ := by
        have hinv : cyclicUnitToBuildingGL P r
            (orderUnitToCyclicUnit P r
              ((normalizedOrderUnit P r u q)⁻¹)) = A⁻¹ := by
          rw [map_inv, map_inv]
        exact (congrArg Units.val hinv).symm
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
