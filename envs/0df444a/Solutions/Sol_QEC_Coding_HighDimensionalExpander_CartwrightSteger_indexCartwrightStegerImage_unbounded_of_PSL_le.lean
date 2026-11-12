-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerImage_unbounded_of_PSL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:19:21.356939+00:00
-- url     : https://prove2.me/submissions/001880ee-c6db-411c-a007-795d4b3e6350

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_PSL_le_indexCartwrightStegerImage_of_le
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_PSL_unbounded


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (hPSL : ∀ level,
      PSL P r level ≤ IndexCartwrightStegerImage P r level)
    (bound : Nat) :
    ∃ level, bound <
      Nat.card (IndexCartwrightStegerImage P r level) := by
  obtain ⟨level, hlevel⟩ := CongruenceLifting.PSL_unbounded P r bound
  exact ⟨level, hlevel.trans_le
    (natCard_PSL_le_indexCartwrightStegerImage_of_le
      P r level (hPSL level))⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
