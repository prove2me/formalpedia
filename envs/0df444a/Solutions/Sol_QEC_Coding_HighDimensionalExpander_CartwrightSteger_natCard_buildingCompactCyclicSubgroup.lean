-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_buildingCompactCyclicSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:04:29.477466+00:00
-- url     : https://prove2.me/submissions/839eff69-6628-483b-8db5-9c9abf8d20a2

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingConstantKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCompactNormalForm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_globalIntegralCompactCyclicSubgroup


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Nat.card (BuildingCompactCyclicSubgroup P r) =
      r.matrixRank * ∑ i ∈ Finset.range r.matrixRank, P.q ^ i := by
  rw [Nat.card_congr (globalIntegralCompactEquivBuildingCompact P r).symm]
  exact natCard_globalIntegralCompactCyclicSubgroup P r
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
