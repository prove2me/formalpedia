-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange.primeFieldMorphism_geometricallyReduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:23:18.528689+00:00
-- url     : https://prove2.me/submissions/317240a8-b116-4045-86a1-8f751983d49d

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedBaseChange_primeFieldPullback_isReduced

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (X : Scheme)
    [_root_.AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (.of (ZMod p))) : GeometricallyReduced f := by
  constructor
  intro K _ g Z fst snd h
  let := primeFieldPullback_isReduced p X f K g
  exact isReduced_of_isOpenImmersion h.isoPullback.hom
end QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
