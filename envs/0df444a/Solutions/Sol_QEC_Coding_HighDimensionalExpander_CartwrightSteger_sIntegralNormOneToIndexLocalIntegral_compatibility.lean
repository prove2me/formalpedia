-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.sIntegralNormOneToIndexLocalIntegral_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:57:44.066102+00:00
-- url     : https://prove2.me/submissions/6cfa032d-52f0-4f8c-a59a-2d4ebb0fbf3c

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraNormOneToIndexLocal_order_compatibility

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : CartwrightStegerSIntegralNormOne P r) :
    (sIntegralNormOneToIndexLocalIntegral P r level u :
        IndexLocalNormOneInnerForm P r level) =
      cyclicAlgebraNormOneToIndexLocal P r level
        (sIntegralNormOneToCyclicAlgebraNormOne P r u) := by
  symm
  exact cyclicAlgebraNormOneToIndexLocal_order_compatibility P r level
    ((orderNormOneInnerFormEquivSIntegralNormOne P r).symm u)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
