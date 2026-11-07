-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalDoubleCoset_rankThree_two_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:21:56.670721+00:00
-- url     : https://prove2.me/submissions/fec74d9e-0b2a-4e05-bd11-cc8ff3a6755d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutationCoweight_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalCoweight_rankThree_two_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_subgroup_doubleCoset_inv_eq_of_inv_eq_conj

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] :
    (fundamentalDoubleCoset k 3 2)⁻¹ =
      fundamentalDoubleCoset k 3 1 := by
  exact subgroup_doubleCoset_inv_eq_of_inv_eq_conj
    (maximalCompact k 3)
    (permutationCoweight_mem_maximalCompact k Fin.revPerm)
    (fundamentalCoweight_rankThree_two_inv k)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
