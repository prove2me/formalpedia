-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.powerSeries_integer_local_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:43:19.504205+00:00
-- url     : https://prove2.me/submissions/9a70cc06-b9d1-4848-b99b-5123a2558b37

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
    {k : Type u} [Field k] {d : ℕ}
    (g : GL (Fin d) (IntegerRing k)) :
    integralGeneralLinearToLocal k d
        (powerSeriesGeneralLinearToInteger k d g) =
      powerSeriesGeneralLinearToLocal k d g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
