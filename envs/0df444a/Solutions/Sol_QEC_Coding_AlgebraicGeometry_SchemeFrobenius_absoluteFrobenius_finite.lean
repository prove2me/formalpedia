-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.SchemeFrobenius.absoluteFrobenius_finite
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:26:50.896775+00:00
-- url     : https://prove2.me/submissions/264658de-efb2-4654-8011-1d2ea68760a3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_PrimeAlgebraFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Geometry.RingedSpace.Stalks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_AbsoluteFrobenius
set_option autoImplicit false
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
variable (p : ℕ) [Fact p.Prime] (X : Scheme) (f : X ⟶ Spec (.of (ZMod p)))

private lemma primeAlgebraFrobenius_constant_aux (R : Type*) [CommRing R]
    [Algebra (ZMod p) R] (a : ZMod p) :
    primeAlgebraFrobenius p R (algebraMap (ZMod p) R a) = algebraMap (ZMod p) R a := by
  change (algebraMap (ZMod p) R a)^p = algebraMap (ZMod p) R a
  rw [← map_pow, ZMod.pow_card]

private lemma primeAlgebraFrobenius_comp_base_aux (R : Type*) [CommRing R]
    [Algebra (ZMod p) R] :
    (primeAlgebraFrobenius p R).comp (algebraMap (ZMod p) R) = algebraMap (ZMod p) R := by
  ext a
  exact primeAlgebraFrobenius_constant_aux p R a

private lemma primeAlgebraFrobenius_integral_aux (R : Type*) [CommRing R]
    [Algebra (ZMod p) R] : (primeAlgebraFrobenius p R).IsIntegral := by
  intro x
  refine ⟨Polynomial.X^p - Polynomial.C x,
    Polynomial.monic_X_pow_sub_C x (Fact.out : p.Prime).ne_zero, ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  change x^p - x^p = 0
  exact sub_self _

private lemma primeAlgebraFrobenius_finite_aux (R : Type*) [CommRing R]
    [Algebra (ZMod p) R] [Algebra.FiniteType (ZMod p) R] :
    (primeAlgebraFrobenius p R).Finite := by
  have hb : (algebraMap (ZMod p) R).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hc : ((primeAlgebraFrobenius p R).comp (algebraMap (ZMod p) R)).FiniteType := by
    rw [primeAlgebraFrobenius_comp_base_aux]
    exact hb
  exact RingHom.finite_iff_isIntegral_and_finiteType.mpr
    ⟨primeAlgebraFrobenius_integral_aux p R, RingHom.FiniteType.of_comp_finiteType hc⟩

private lemma sectionBase_finiteType_aux [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) : (sectionBase p X f U).FiniteType := by
  have hbase := f.finiteType_appLE (isAffineOpen_top _) hU (show U ≤ f ⁻¹ᵁ ⊤ from le_top)
  have hiso : (Scheme.ΓSpecIso (.of (ZMod p))).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (ZMod p))).inv).surjective
  exact hbase.comp hiso

theorem solution [LocallyOfFiniteType f] :
    IsFinite (absoluteFrobenius p X f) := by
  refine { isAffine_preimage := ?_, finite_app := ?_ }
  · intro U hU
    exact hU
  · intro U hU
    let : Algebra (ZMod p) Γ(X, U) := (sectionBase p X f U).toAlgebra
    let : Algebra.FiniteType (ZMod p) Γ(X, U) := sectionBase_finiteType_aux p X f U hU
    exact primeAlgebraFrobenius_finite_aux p Γ(X, U)
