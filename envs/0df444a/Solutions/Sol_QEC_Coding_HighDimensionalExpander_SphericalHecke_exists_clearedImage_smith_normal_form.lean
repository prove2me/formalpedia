-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.exists_clearedImage_smith_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:58:18.751998+00:00
-- url     : https://prove2.me/submissions/e65349c6-8859-4942-bbab-19a4fd57164a

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
    (A : GL (Fin d) (LocalFunctionField k)) :
    ∃ (ambientBasis : Basis (Fin d) (IntegerRing k) (Fin d → IntegerRing k))
      (diagonalCoeff : Fin d → IntegerRing k)
      (imageBasis : Basis (Fin d) (IntegerRing k)
        (clearedImage (k := k) (d := d) A)),
      ∀ i, (imageBasis i : Fin d → IntegerRing k) =
        diagonalCoeff i • ambientBasis i := by
  exact (clearedImage (k := k) (d := d) A).exists_smith_normal_form_of_rank_eq
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
