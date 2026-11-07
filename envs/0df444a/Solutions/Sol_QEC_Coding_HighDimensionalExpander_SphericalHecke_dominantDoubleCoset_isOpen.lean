-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.dominantDoubleCoset_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:48:03.00883+00:00
-- url     : https://prove2.me/submissions/0e5af6af-c3e1-4198-a780-d50f06e4a91d

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
    (k : Type u) [Field k] [Finite k] {d : ℕ}
    (weight : DominantCoweight d) : IsOpen (dominantDoubleCoset k weight) := by
  exact ((maximalCompact_isOpen k d).mul_right).mul_right
end QEC.Coding.HighDimensionalExpander.SphericalHecke
