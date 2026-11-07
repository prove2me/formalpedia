-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:29:08.739906+00:00
-- url     : https://prove2.me/submissions/65bb2479-5657-4a64-aa96-55365af389fe

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
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups Pointwise
universe u
open scoped LocalTopology
open MeasureTheory
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution (R : Type u) [CommRing R] (d : ℕ)
    (u : Fin d → Units R) (i j : Fin d) :
    diagonalGeneralLinear R d u i j = if i = j then (u i : R) else 0 := by
  simp [diagonalGeneralLinear, Matrix.diagonal]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
