-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveTranspose_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:13:09.477717+00:00
-- url     : https://prove2.me/submissions/7d41402b-1640-46d0-a861-f47519333866

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_isInvInvariant
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveContragredient_measurePreserving

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] [Finite k] {d : ℕ} (hd : 0 < d) :
    MeasureTheory.MeasurePreserving projectiveTranspose
      (normalizedLocalHaarMeasure k d)
      (normalizedLocalHaarMeasure k d) := by
  letI : MeasureTheory.Measure.IsInvInvariant
      (normalizedLocalHaarMeasure k d) :=
    normalizedLocalHaarMeasure_isInvInvariant k hd
  exact projectiveContragredient_measurePreserving.comp
    (MeasureTheory.Measure.measurePreserving_inv
      (normalizedLocalHaarMeasure k d))
end QEC.Coding.HighDimensionalExpander.SphericalHecke
