-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.integerEmbedding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:51:36.707206+00:00
-- url     : https://prove2.me/submissions/95deba3c-74f7-4455-8ea3-b32273a50f7c

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
theorem _root_.solution (k : Type u) [CommRing k] :
    Function.Injective (integerEmbedding k) :=
  HahnSeries.ofPowerSeries_injective
end QEC.Coding.HighDimensionalExpander.SphericalHecke
