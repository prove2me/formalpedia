-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorInverseMatrix_mem_cyclicAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:44.954306+00:00
-- url     : https://prove2.me/submissions/3b7a32eb-9d1d-4e3d-bb74-77929125ac79

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    cyclicGeneratorInverseMatrix P r ∈ CyclicAlgebra P r := by
  apply Algebra.subset_adjoin
  exact Set.mem_union_right _ (Set.mem_insert_iff.mpr (Or.inr rfl))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
