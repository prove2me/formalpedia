-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.normalizedLocalHaarMeasure_isInvInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:12:13.491523+00:00
-- url     : https://prove2.me/submissions/efec98a5-963f-42b6-b220-69f70b66388a

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_isMulRightInvariant
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
    (k : Type u) [Field k] [Finite k] {d : ℕ} (hd : 0 < d) :
    MeasureTheory.Measure.IsInvInvariant
      (normalizedLocalHaarMeasure k d) := by
  letI : MeasureTheory.Measure.IsMulRightInvariant
      (normalizedLocalHaarMeasure k d) :=
    normalizedLocalHaarMeasure_isMulRightInvariant k hd
  constructor
  let μ := normalizedLocalHaarMeasure k d
  let c : ENNReal := MeasureTheory.Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ :=
    MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_innerRegular μ.inv μ
  have heval := congrArg
    (fun ν : MeasureTheory.Measure PGL(Fin d, LocalFunctionField k) =>
      ν (maximalCompact k d)) hc
  have hc_one : c = 1 := by
    dsimp [μ] at heval
    rw [MeasureTheory.Measure.inv_apply, inv_coe_set,
      normalizedLocalHaarMeasure_maximalCompact] at heval
    simpa using heval.symm
  exact hc.trans (by rw [hc_one, one_smul])
end QEC.Coding.HighDimensionalExpander.SphericalHecke
