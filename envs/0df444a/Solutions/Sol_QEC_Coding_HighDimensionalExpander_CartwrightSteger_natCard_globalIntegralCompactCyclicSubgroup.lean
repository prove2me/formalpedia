-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_globalIntegralCompactCyclicSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:21:01.289995+00:00
-- url     : https://prove2.me/submissions/c3465353-41a0-4142-90ef-e2d964d1722e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactGroup
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_CompactNormalForm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_constantProjectiveClass


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Nat.card (GlobalIntegralCompactCyclicSubgroup P r) =
      r.matrixRank * ∑ i ∈ Finset.range r.matrixRank, P.q ^ i := by
  rw [Nat.card_congr (globalIntegralProjectiveNormalFormEquiv P r).symm,
    Nat.card_prod, Nat.card_fin, natCard_constantProjectiveClass]
  exact Nat.mul_comm _ _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
