-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_rankThree_eq_of_doubleCoset_inter_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:10:28.079171+00:00
-- url     : https://prove2.me/submissions/0261774b-52fd-4034-b6e5-d04252233aa3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_first_exponent_eq_of_doubleCoset_inter_nonempty
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_exponent_sum_eq_of_doubleCoset_inter_nonempty
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k]
    (a b : ProjectiveDominantCoweight 2)
    (hinter : (projectiveDominantDoubleCoset k a ∩
      projectiveDominantDoubleCoset k b).Nonempty) :
    a = b := by
  have hfirst :=
    projectiveDominant_first_exponent_eq_of_doubleCoset_inter_nonempty
      k a b hinter
  have hsum :=
    projectiveDominant_exponent_sum_eq_of_doubleCoset_inter_nonempty
      k a b hinter
  have halast : a.toDominant.exponent (2 : Fin 3) = 0 := by
    simpa using a.last_exponent_eq_zero
  have hblast : b.toDominant.exponent (2 : Fin 3) = 0 := by
    simpa using b.last_exponent_eq_zero
  apply ProjectiveDominantCoweight.ext
  funext i
  fin_cases i
  · exact hfirst
  · simp [Fin.sum_univ_succ, halast, hblast] at hsum
    change a.toDominant.exponent (1 : Fin 3) =
      b.toDominant.exponent (1 : Fin 3)
    omega
  · exact halast.trans hblast.symm
end QEC.Coding.HighDimensionalExpander.SphericalHecke
