-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_mem_group
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:55.294221+00:00
-- url     : https://prove2.me/submissions/3ce5f781-eb5d-45cc-8bed-395f9eb790c1

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    cartwrightStegerGenerator P r u ∈ CartwrightStegerMatrixGroup P r :=
  Subgroup.subset_closure ⟨u, rfl⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
