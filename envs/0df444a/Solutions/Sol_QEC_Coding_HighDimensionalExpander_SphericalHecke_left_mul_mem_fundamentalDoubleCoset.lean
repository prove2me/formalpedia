-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.left_mul_mem_fundamentalDoubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:46:29.906612+00:00
-- url     : https://prove2.me/submissions/62e24839-3017-49f3-bc63-7b48c47da007

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups Pointwise
universe u
open scoped LocalTopology
open MeasureTheory
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    {h x : PGL(Fin d, LocalFunctionField k)}
    (hh : h ∈ maximalCompact k d)
    (hx : x ∈ fundamentalDoubleCoset k d r) :
    h * x ∈ fundamentalDoubleCoset k d r := by
  rw [fundamentalDoubleCoset] at hx ⊢
  rcases hx with ⟨y, hy, z, hz, rfl⟩
  rcases hy with ⟨a, ha, b, hb, rfl⟩
  refine ⟨(h * a) * b, ?_, z, hz, ?_⟩
  · exact ⟨h * a, (maximalCompact k d).mul_mem hh ha,
      b, hb, rfl⟩
  · simp [mul_assoc]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
