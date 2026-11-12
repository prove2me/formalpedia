-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.image_preimage_arithmeticFiniteAdeleCyclicIntegralNormOneSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:53:03.882402+00:00
-- url     : https://prove2.me/submissions/f62ca896-9545-4f10-a9f1-c53f69c2fedd

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
    (P : BasePrime) (r : Rank) :
    cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r ''
        (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r) ⁻¹'
          ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r =
      Set.range (orderNormOneInnerFormToArithmeticFiniteAdeleNormOne P r) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    change cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u ∈
      ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r at hu
    rw [cyclicAlgebraNormOne_preimage_integralNormOneSet] at hu
    obtain ⟨s, rfl⟩ := hu
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨orderNormOneInnerFormToCyclicAlgebraNormOne P r s, ?_, rfl⟩
    change cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r
        (orderNormOneInnerFormToCyclicAlgebraNormOne P r s) ∈
      ArithmeticFiniteAdeleCyclicIntegralNormOneSet P r
    rw [cyclicAlgebraNormOne_preimage_integralNormOneSet]
    exact ⟨s, rfl⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
