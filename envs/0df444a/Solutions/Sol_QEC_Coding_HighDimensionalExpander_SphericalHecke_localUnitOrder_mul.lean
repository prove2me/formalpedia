-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.localUnitOrder_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:41:57.608291+00:00
-- url     : https://prove2.me/submissions/de84b8a7-a587-42a7-ab88-f785b8c1bcde

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k]
    (a b : Units (LocalFunctionField k)) :
    localUnitOrder (a * b) = localUnitOrder a + localUnitOrder b := by
  exact HahnSeries.order_mul a.ne_zero b.ne_zero
end QEC.Coding.HighDimensionalExpander.SphericalHecke
