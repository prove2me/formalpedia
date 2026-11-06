-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange.primeFieldPullback_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:58:43.257955+00:00
-- url     : https://prove2.me/submissions/c1e0a4a8-b66e-448a-a45e-3237d93724ee

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeReducedBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_PrimeReducedBaseChange_primeSpecPullback_isReduced

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (X : Scheme)
    [_root_.AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (.of (ZMod p))) (K : Type) [Field K]
    (g : Spec (.of K) ⟶ Spec (.of (ZMod p))) :
    _root_.AlgebraicGeometry.IsReduced (pullback f g) := by
  wlog hX : ∃ R : CommRingCat, X = Spec R generalizing f X
  · let U := X.affineCover.pullback₁ (pullback.fst f g)
    let : ∀ i, _root_.AlgebraicGeometry.IsReduced (U.X i) := fun i => by
      have hAffine := this
      let : IsOpenImmersion (X.affineCover.f i) := X.affineCover.map_prop i
      let : _root_.AlgebraicGeometry.IsReduced (X.affineCover.X i) :=
        isReduced_of_isOpenImmersion (X.affineCover.f i)
      have h : _root_.AlgebraicGeometry.IsReduced
          (pullback (X.affineCover.f i ≫ f) g) :=
        hAffine (X.affineCover.X i) (X.affineCover.f i ≫ f) ⟨_, rfl⟩
      let := h
      have hChart : _root_.AlgebraicGeometry.IsReduced
          (pullback (X.affineCover.f i) (pullback.fst f g)) :=
        isReduced_of_isOpenImmersion
          (pullbackRightPullbackFstIso f g (X.affineCover.f i)).hom
      let := hChart
      change _root_.AlgebraicGeometry.IsReduced
        (pullback (pullback.fst f g) (X.affineCover.f i))
      exact ObjectProperty.prop_of_iso (P := fun Y : Scheme => _root_.AlgebraicGeometry.IsReduced Y)
        (pullbackSymmetry (pullback.fst f g) (X.affineCover.f i)).symm hChart
    exact _root_.AlgebraicGeometry.IsReduced.of_openCover _ U
  · obtain ⟨R, rfl⟩ := hX
    let : _root_.IsReduced R :=
      (affine_isReduced_iff R).mp (inferInstance : _root_.AlgebraicGeometry.IsReduced (Spec R))
    exact primeSpecPullback_isReduced p R K f g
end QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
