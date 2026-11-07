-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_isMulRightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:11:26.107739+00:00
-- url     : https://prove2.me/submissions/c98410a0-754b-4d9b-82af-1a8540391229

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_modularCharacter_eq_one

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d) :
    MeasureTheory.Measure.IsMulRightInvariant
      (normalizedLocalHaarMeasure k d) := by
  constructor
  intro g
  rw [MeasureTheory.Measure.map_right_mul_eq_modularCharacterFun_smul]
  change (MeasureTheory.Measure.modularCharacter g : NNReal) •
      normalizedLocalHaarMeasure k d = normalizedLocalHaarMeasure k d
  rw [modularCharacter_eq_one k hd g, one_smul]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
