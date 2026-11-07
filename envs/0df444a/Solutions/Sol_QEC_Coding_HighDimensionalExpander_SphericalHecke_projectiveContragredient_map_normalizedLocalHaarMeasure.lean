-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveContragredient_map_normalizedLocalHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:06:55.510525+00:00
-- url     : https://prove2.me/submissions/ea6c19c7-bb4f-4cf7-9f3b-9754e5fd261f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveContragredient_preimage_maximalCompact
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
    {k : Type u} [Field k] [Finite k] {d : ℕ} :
    MeasureTheory.Measure.map projectiveContragredientHom
        (normalizedLocalHaarMeasure k d) =
      normalizedLocalHaarMeasure k d := by
  let μ := normalizedLocalHaarMeasure k d
  let ν := MeasureTheory.Measure.map projectiveContragredientHom μ
  letI : MeasureTheory.Measure.IsHaarMeasure ν :=
    (projectiveContragredientEquiv :
      PGL(Fin d, LocalFunctionField k) ≃* _).isHaarMeasure_map
        μ continuous_projectiveContragredient
          continuous_projectiveContragredient
  let c : ENNReal := MeasureTheory.Measure.haarScalarFactor ν μ
  have hc : ν = c • μ :=
    MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_innerRegular ν μ
  have heval := congrArg
    (fun m : MeasureTheory.Measure PGL(Fin d, LocalFunctionField k) ↦
      m (maximalCompact k d)) hc
  have hν : ν (maximalCompact k d) = 1 := by
    dsimp [ν]
    rw [MeasureTheory.Measure.map_apply
      continuous_projectiveContragredient.measurable
      (maximalCompact_isOpen k d).measurableSet]
    rw [projectiveContragredient_preimage_maximalCompact,
      normalizedLocalHaarMeasure_maximalCompact]
  have hc_one : c = 1 := by
    change ν (maximalCompact k d) =
      (c • μ) (maximalCompact k d) at heval
    rw [hν] at heval
    dsimp [μ] at heval
    rw [normalizedLocalHaarMeasure_maximalCompact] at heval
    simpa using heval.symm
  exact hc.trans (by rw [hc_one, one_smul])
end QEC.Coding.HighDimensionalExpander.SphericalHecke
