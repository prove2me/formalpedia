-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:28:14.515202+00:00
-- url     : https://prove2.me/submissions/aa978b31-885d-4c8c-9131-0cea34572840

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
theorem _root_.solution (k : Type u) [Field k] :
    (uniformizerUnit k : LocalFunctionField k) =
      HahnSeries.single (1 : Int) 1 :=
  rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
