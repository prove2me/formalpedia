-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.prod_coordinateUniformizerCoweight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:35.777626+00:00
-- url     : https://prove2.me/submissions/5c39e852-7023-4115-bc04-cd28716554d4

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_prod_coordinateUniformizerGeneralLinear

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] (d : ℕ) :
    ((List.finRange d).map
        (coordinateUniformizerCoweight k d)).prod = 1 := by
  calc
    ((List.finRange d).map
        (coordinateUniformizerCoweight k d)).prod =
        Matrix.ProjGenLinGroup.mk
          (((List.finRange d).map
            (coordinateUniformizerGeneralLinear k d)).prod) := by
      exact List.prod_map_hom (List.finRange d)
        (coordinateUniformizerGeneralLinear k d)
        Matrix.ProjGenLinGroup.mk
    _ = Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.scalar (Fin d) (uniformizerUnit k)) := by
      rw [prod_coordinateUniformizerGeneralLinear]
    _ = 1 := Matrix.ProjGenLinGroup.mk_scalar _
end QEC.Coding.HighDimensionalExpander.SphericalHecke
