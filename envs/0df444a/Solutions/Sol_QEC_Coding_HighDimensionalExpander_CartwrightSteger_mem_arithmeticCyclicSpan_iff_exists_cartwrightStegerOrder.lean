-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_arithmeticCyclicSpan_iff_exists_cartwrightStegerOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:52:35.146203+00:00
-- url     : https://prove2.me/submissions/6d7a9e1c-b8a3-482b-92a0-42bcfc5b8892

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    x ∈ arithmeticCyclicSpan P r ↔
      ∃ y : CartwrightStegerOrder P r,
        cartwrightStegerOrderToCyclicAlgebra P r y = x := by
  constructor
  · exact exists_cartwrightStegerOrder_of_mem_arithmeticCyclicSpan P r x
  · rintro ⟨y, rfl⟩
    exact cartwrightStegerOrderToCyclic_mem_arithmeticCyclicSpan P r y
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
