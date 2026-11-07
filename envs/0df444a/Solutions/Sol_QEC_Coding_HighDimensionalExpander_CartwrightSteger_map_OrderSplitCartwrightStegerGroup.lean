-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_OrderSplitCartwrightStegerGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:41.923326+00:00
-- url     : https://prove2.me/submissions/197a6abf-6b3f-4cc0-a8c5-20eab163ca84

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderSplitCartwrightStegerGroup P r).map
        (orderSplitReductionPGLHom P r level) =
      IndexCartwrightStegerImage P r level := by
  rw [OrderSplitCartwrightStegerGroup, MonoidHom.map_closure,
    ← IndexCartwrightStegerUnitImage_eq_image,
    IndexCartwrightStegerUnitImage]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (orderSplitReductionPGLHom_generator P r level u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨orderSplitCartwrightStegerGeneratorGL P r u,
      ⟨u, rfl⟩, orderSplitReductionPGLHom_generator P r level u⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
