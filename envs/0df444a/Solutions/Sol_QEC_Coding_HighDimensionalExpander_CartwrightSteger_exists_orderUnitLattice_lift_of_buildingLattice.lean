-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_orderUnitLattice_lift_of_buildingLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:42:31.384845+00:00
-- url     : https://prove2.me/submissions/2dcbc7bf-bd9f-4d3f-9719-affe1cccd17f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderUnitLattice_to_building

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (g : BuildingCartwrightStegerLattice P r) :
    ∃ u : (CartwrightStegerOrder P r)ˣ,
      u ∈ CartwrightStegerOrderUnitLattice P r ∧
      orderUnitToBuildingPGL P r u = g := by
  have hg : (g : Matrix.ProjGenLinGroup (Fin r.matrixRank)
      (BuildingLocalField P)) ∈
      (CartwrightStegerOrderUnitLattice P r).map
        (orderUnitToBuildingPGL P r) := by
    rw [map_orderUnitLattice_to_building]
    exact g.property
  obtain ⟨u, hu, hmap⟩ := hg
  exact ⟨u, hu, hmap⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
