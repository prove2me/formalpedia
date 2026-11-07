-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantDoubleCoset_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:48:54.759551+00:00
-- url     : https://prove2.me/submissions/b2058382-a441-448b-bfaf-f620adcd967d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantDoubleCoset_isOpen

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    IsOpen (projectiveDominantDoubleCoset k weight) :=
  dominantDoubleCoset_isOpen k weight.toDominant
end QEC.Coding.HighDimensionalExpander.SphericalHecke
