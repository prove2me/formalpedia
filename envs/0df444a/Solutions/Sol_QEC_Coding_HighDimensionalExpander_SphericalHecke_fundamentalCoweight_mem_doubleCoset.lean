-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalCoweight_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:00:45.769312+00:00
-- url     : https://prove2.me/submissions/69f6ed5a-3567-4faa-a479-ccdd1cea14e7

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups Pointwise
universe u
open scoped LocalTopology
open MeasureTheory
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] (d r : ℕ) :
    fundamentalCoweight k d r ∈ fundamentalDoubleCoset k d r := by
  rw [fundamentalDoubleCoset, Set.mem_mul]
  refine ⟨fundamentalCoweight k d r, ?_, 1, (maximalCompact k d).one_mem, mul_one _⟩
  rw [Set.mem_mul]
  exact ⟨1, (maximalCompact k d).one_mem, fundamentalCoweight k d r,
    Set.mem_singleton _, one_mul _⟩
end QEC.Coding.HighDimensionalExpander.SphericalHecke
