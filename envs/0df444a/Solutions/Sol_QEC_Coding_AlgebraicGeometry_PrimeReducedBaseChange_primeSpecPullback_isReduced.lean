-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange.primeSpecPullback_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:57:51.78005+00:00
-- url     : https://prove2.me/submissions/83fa6516-382d-44fe-8bb3-63b401c65409

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedTensor_primeReducedTensor_isReduced

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (C K : Type) [CommRing C] [Field K]
    [_root_.IsReduced C]
    (f : Spec (.of C) ⟶ Spec (.of (ZMod p)))
    (g : Spec (.of K) ⟶ Spec (.of (ZMod p))) :
    _root_.AlgebraicGeometry.IsReduced (pullback f g) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom, ψ.hom]
  let := PrimeReducedTensor.primeReducedTensor_isReduced p C K
  exact isReduced_of_isOpenImmersion (pullbackSpecIso (ZMod p) C K).hom
end QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
