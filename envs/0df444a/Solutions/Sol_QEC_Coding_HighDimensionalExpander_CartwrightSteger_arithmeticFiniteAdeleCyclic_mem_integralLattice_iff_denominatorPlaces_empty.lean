-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFiniteAdeleCyclic_mem_integralLattice_iff_denominatorPlaces_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:37:22.823371+00:00
-- url     : https://prove2.me/submissions/f734359c-2da8-48ce-b394-39ecbe9cf7b1

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.IsOpenUnits
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    x ∈ ArithmeticFiniteAdeleCyclicIntegralLattice P r ↔
      arithmeticFiniteAdeleCyclicNonintegralPlaces P r x = ∅ := by
  constructor
  · intro hx
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨p, hp⟩ := hv
    exact hp (hx p v)
  · intro h p v
    by_contra hp
    have hv : v ∈ arithmeticFiniteAdeleCyclicNonintegralPlaces P r x :=
      ⟨p, hp⟩
    rw [h] at hv
    exact hv
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
