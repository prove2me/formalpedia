-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_OrderSplitCartwrightStegerLattice_to_global
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:33.967353+00:00
-- url     : https://prove2.me/submissions/d12fae1c-0ec5-4738-be78-5b19662dac12

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitCartwrightStegerClassGeneratorGL_to_global

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    (OrderSplitCartwrightStegerLattice P r).map
        (orderSplitBaseChangeGLHom P r) =
      CartwrightStegerMatrixGroup P r := by
  rw [OrderSplitCartwrightStegerLattice, MonoidHom.map_closure,
    CartwrightStegerMatrixGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u,
      (map_orderSplitCartwrightStegerClassGeneratorGL_to_global
        P r u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨orderSplitCartwrightStegerGeneratorGL P r
        (constantClassRepresentative P r u),
      ⟨u, rfl⟩,
      map_orderSplitCartwrightStegerClassGeneratorGL_to_global P r u⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
