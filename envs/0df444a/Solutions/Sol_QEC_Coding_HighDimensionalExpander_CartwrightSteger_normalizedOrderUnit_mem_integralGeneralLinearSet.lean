-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.normalizedOrderUnit_mem_integralGeneralLinearSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:54:04.844103+00:00
-- url     : https://prove2.me/submissions/b68922f1-dd71-4b51-9228-60159d50d840

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_normalizedOrderUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_localDetOrder_normalizedOrderUnit_eq_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projective_mk_mem_maximalCompact_iff_integral


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
    cyclicUnitToBuildingGL P r
        (orderUnitToCyclicUnit P r (normalizedOrderUnit P r u q)) ∈
      SphericalHecke.integralGeneralLinearSet
        (BaseField P) r.matrixRank := by
  let A := cyclicUnitToBuildingGL P r
    (orderUnitToCyclicUnit P r (normalizedOrderUnit P r u q))
  have hdet : SphericalHecke.localUnitOrder
      (Matrix.GeneralLinearGroup.det A) = 0 :=
    localDetOrder_normalizedOrderUnit_eq_zero P r u q hq
  apply (SphericalHecke.projective_mk_mem_maximalCompact_iff_integral
    (BaseField P) r.matrixRank
    (lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)) A hdet).mp
  change orderUnitToBuildingPGL P r
      (normalizedOrderUnit P r u q) ∈
    SphericalHecke.maximalCompact (BaseField P) r.matrixRank
  rw [orderUnitToBuildingPGL_normalizedOrderUnit]
  exact hcompact
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
