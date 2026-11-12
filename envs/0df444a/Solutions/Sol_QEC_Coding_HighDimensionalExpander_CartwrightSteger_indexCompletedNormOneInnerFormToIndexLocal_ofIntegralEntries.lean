-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCompletedNormOneInnerFormToIndexLocal_ofIntegralEntries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:16:47.341817+00:00
-- url     : https://prove2.me/submissions/49500a52-6044-41d0-ab5a-1321898b1824

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
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexLocalNormOneInnerForm P r level)
    (hs : ∀ i j,
      ((s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (IndexCongruenceLocalField P r level)) i j) ∈
          IndexCongruenceLocalIntegers P r level) :
    indexCompletedNormOneInnerFormToIndexLocal P r level
        (indexLocalNormOneToCompletedOfIntegralEntries P r level s hs) = s := by
  apply Subtype.ext
  exact indexLocalIntegralEntriesToPowerSeriesMatrix_map P r level s hs
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
