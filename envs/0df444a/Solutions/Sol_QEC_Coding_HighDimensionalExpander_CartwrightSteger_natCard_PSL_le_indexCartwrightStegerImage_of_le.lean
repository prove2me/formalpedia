-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_PSL_le_indexCartwrightStegerImage_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:16:29.639053+00:00
-- url     : https://prove2.me/submissions/dd303f20-7615-462d-b7a3-af2ee38bee6b

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
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    Nat.card (PSL P r level) ≤
      Nat.card (IndexCartwrightStegerImage P r level) := by
  letI : Finite (PGL P r level) :=
    Finite.of_surjective
      (Matrix.ProjGenLinGroup.mk :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ResidueField P r level) → PGL P r level)
      Matrix.ProjGenLinGroup.mk_surjective
  letI : Finite (IndexCartwrightStegerImage P r level) :=
    Finite.of_injective
      (fun g : IndexCartwrightStegerImage P r level =>
        (g : PGL P r level))
      Subtype.val_injective
  exact Nat.card_le_card_of_injective
    (fun s : PSL P r level =>
      (⟨s, hPSL s.property⟩ : IndexCartwrightStegerImage P r level))
    (fun _ _ h => Subtype.ext <| congrArg
      (fun g : IndexCartwrightStegerImage P r level =>
        (g : PGL P r level)) h)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
