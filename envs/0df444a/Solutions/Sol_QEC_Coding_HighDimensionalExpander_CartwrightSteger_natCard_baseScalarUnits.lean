-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_baseScalarUnits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:34.132716+00:00
-- url     : https://prove2.me/submissions/a9e7eba1-e3c8-4711-9332-dda3d433ec02

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_baseScalarUnitHom_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    Nat.card (baseScalarUnits P r) = P.q - 1 := by
  calc
    Nat.card (baseScalarUnits P r) =
        Nat.card (Units (BaseField P)) :=
      (Nat.card_congr
        (Equiv.ofInjective (baseScalarUnitHom P r)
          (baseScalarUnitHom_injective P r))).symm
    _ = Nat.card (BaseField P) - 1 := Nat.card_units _
    _ = P.q - 1 := by rw [Nat.card_zmod]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
