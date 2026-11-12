-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToBuildingPGL_mem_compactCyclicSubgroup_of_mem_maximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:59:43.834664+00:00
-- url     : https://prove2.me/submissions/7fe9891b-91e3-4c27-8e5a-e58fc69c353a

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToBuildingPGL_normalizedOrderUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_normalizedOrderUnit_buildingIntegral_witnesses
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_localDetOrder_quotient_of_orderUnit_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicOrderUnitToBuildingPGL_mem_compactCyclicSubgroup


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank) :
    orderUnitToBuildingPGL P r u ∈
      BuildingCompactCyclicSubgroup P r := by
  obtain ⟨q, hq⟩ :=
    exists_localDetOrder_quotient_of_orderUnit_mem_maximalCompact
      P r u hcompact
  obtain ⟨hlocal, hlocalInv⟩ :=
    normalizedOrderUnit_buildingIntegral_witnesses
      P r u q hcompact hq
  have hmem := cyclicOrderUnitToBuildingPGL_mem_compactCyclicSubgroup
    P r (normalizedOrderUnit P r u q) hlocal hlocalInv
  change orderUnitToBuildingPGL P r (normalizedOrderUnit P r u q) ∈
    BuildingCompactCyclicSubgroup P r at hmem
  rw [orderUnitToBuildingPGL_normalizedOrderUnit] at hmem
  exact hmem
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
