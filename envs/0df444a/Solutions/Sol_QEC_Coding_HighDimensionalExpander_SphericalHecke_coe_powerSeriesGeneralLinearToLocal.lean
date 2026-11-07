-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_powerSeriesGeneralLinearToLocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:45:04.36597+00:00
-- url     : https://prove2.me/submissions/c64cb58c-16d4-47f8-8f70-57d61cdd8030

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
    {k : Type u} [CommRing k] {d : ℕ}
    (g : GL (Fin d) (IntegerRing k)) :
    (powerSeriesGeneralLinearToLocal k d g :
      Matrix (Fin d) (Fin d) (LocalFunctionField k)) =
      (integerEmbedding k).mapMatrix
        (g : Matrix (Fin d) (Fin d) (IntegerRing k)) := by
  rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
