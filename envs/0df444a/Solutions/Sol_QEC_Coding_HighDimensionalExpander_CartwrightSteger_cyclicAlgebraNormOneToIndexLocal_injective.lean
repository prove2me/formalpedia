-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraNormOneToIndexLocal_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:01:35.56069+00:00
-- url     : https://prove2.me/submissions/dbc3418a-ae63-4c09-8503-5aa09082d851

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraNormOneToSplittingSL_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (cyclicAlgebraNormOneToIndexLocal P r level) := by
  intro u v huv
  apply cyclicAlgebraNormOneToSplittingSL_injective P r
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  apply RingHom.injective
    (splittingFunctionFieldToIndexCongruenceLocalField P r level)
  exact congrArg (fun M : IndexLocalNormOneInnerForm P r level =>
    ((M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (IndexCongruenceLocalField P r level)) i j)) huv
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
