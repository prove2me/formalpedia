-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveContragredient_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:07:42.170488+00:00
-- url     : https://prove2.me/submissions/bf253b84-5ae4-44c1-8c15-6513aa6e9fe5

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveContragredient_map_normalizedLocalHaarMeasure

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] [Finite k] {d : ℕ} :
    MeasureTheory.MeasurePreserving projectiveContragredientHom
      (normalizedLocalHaarMeasure k d)
      (normalizedLocalHaarMeasure k d) :=
  ⟨continuous_projectiveContragredient.measurable,
    projectiveContragredient_map_normalizedLocalHaarMeasure⟩
end QEC.Coding.HighDimensionalExpander.SphericalHecke
