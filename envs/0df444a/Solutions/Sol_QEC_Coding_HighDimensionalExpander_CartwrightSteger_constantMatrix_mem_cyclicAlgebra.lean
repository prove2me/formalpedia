-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantMatrix_mem_cyclicAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:01.661205+00:00
-- url     : https://prove2.me/submissions/a427a426-b4c9-4165-bb8b-6e97bbfaf047

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    constantMatrix P r c ∈ CyclicAlgebra P r := by
  apply Algebra.subset_adjoin
  exact Set.mem_union_left _ ⟨c, rfl⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
