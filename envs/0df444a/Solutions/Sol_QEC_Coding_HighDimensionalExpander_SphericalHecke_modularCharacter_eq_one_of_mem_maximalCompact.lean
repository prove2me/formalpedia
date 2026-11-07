-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.modularCharacter_eq_one_of_mem_maximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:03:53.94421+00:00
-- url     : https://prove2.me/submissions/f3f1c03d-536d-4968-bec0-3ebc510ccc05

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
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
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (h : PGL(Fin d, LocalFunctionField k)) (hh : h ∈ maximalCompact k d) :
    MeasureTheory.Measure.modularCharacter h = 1 := by
  let μ := normalizedLocalHaarMeasure k d
  have hmeasure :=
    MeasureTheory.Measure.map_right_mul_eq_modularCharacterFun_smul μ h
  have hK : MeasurableSet
      (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) :=
    (maximalCompact_isOpen k d).measurableSet
  have heval := congrArg
    (fun ν : MeasureTheory.Measure PGL(Fin d, LocalFunctionField k) =>
      ν (maximalCompact k d)) hmeasure
  change (MeasureTheory.Measure.map (fun x => x * h) μ)
      (maximalCompact k d) =
    (MeasureTheory.Measure.modularCharacterFun h • μ)
      (maximalCompact k d) at heval
  rw [MeasureTheory.Measure.map_apply (measurable_mul_const h) hK] at heval
  have hpre :
      (fun x : PGL(Fin d, LocalFunctionField k) => x * h) ⁻¹'
          (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) =
        (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) := by
    ext x
    change x * h ∈ maximalCompact k d ↔ x ∈ maximalCompact k d
    constructor
    · intro hx
      simpa using (maximalCompact k d).mul_mem hx
        ((maximalCompact k d).inv_mem hh)
    · intro hx
      exact (maximalCompact k d).mul_mem hx hh
  dsimp [μ] at heval
  rw [hpre, normalizedLocalHaarMeasure_maximalCompact] at heval
  change MeasureTheory.Measure.modularCharacterFun h = 1
  apply ENNReal.coe_injective
  simpa using heval.symm
end QEC.Coding.HighDimensionalExpander.SphericalHecke
