-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_coordinateUniformizer_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:05:42.22149+00:00
-- url     : https://prove2.me/submissions/d2ed0c9e-31ce-4b75-8bbe-992cb6ebae7f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coordinateUniformizerCoweight_conj
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_monoidHom_conj_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] {d : ℕ} (i j : Fin d) :
    MeasureTheory.Measure.modularCharacter
        (coordinateUniformizerCoweight k d i) =
      MeasureTheory.Measure.modularCharacter
        (coordinateUniformizerCoweight k d j) := by
  rw [← coordinateUniformizerCoweight_conj k i j]
  exact (monoidHom_conj_eq
    (MeasureTheory.Measure.modularCharacter :
      PGL(Fin d, LocalFunctionField k) →* NNReal)
    (permutationCoweight k (Equiv.swap i j))
    (coordinateUniformizerCoweight k d i)).symm
end QEC.Coding.HighDimensionalExpander.SphericalHecke
