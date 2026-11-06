-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.baseRationalPlace_order_algebraMap_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:00:56.532215+00:00
-- url     : https://prove2.me/submissions/4a1f0bc2-af4c-4945-99b8-6b446faa4b09

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem basePolynomialIdealMultiplicity_eq_rootMultiplicity
    (a : BasePoint) (p : F256[X]) (hp : p ≠ 0) :
    multiplicity (Ideal.span ({X - C (a : F256)} : Set F256[X]))
        (Ideal.span ({p} : Set F256[X])) =
      p.rootMultiplicity (a : F256) := by
  letI : DecidableEq F256 := Classical.decEq F256
  rw [Polynomial.rootMultiplicity_eq_multiplicity, if_neg hp]
  have hq : Irreducible (X - C (a : F256) : F256[X]) :=
    irreducible_X_sub_C (a : F256)
  have hqprime : Prime (X - C (a : F256) : F256[X]) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hspanprime : Prime
      (Ideal.span ({X - C (a : F256)} : Set F256[X])) := by
    rw [Ideal.prime_span_singleton_iff]
    exact hqprime
  have hpSpan : Ideal.span ({p} : Set F256[X]) ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt hp
  have hfiniteElement : FiniteMultiplicity
      (X - C (a : F256) : F256[X]) p :=
    Polynomial.finiteMultiplicity_X_sub_C (a : F256) hp
  have hfiniteIdeal : FiniteMultiplicity
      (Ideal.span ({X - C (a : F256)} : Set F256[X]))
      (Ideal.span ({p} : Set F256[X])) :=
    FiniteMultiplicity.of_prime_left hspanprime hpSpan
  apply Nat.cast_injective (R := ℕ∞)
  rw [← hfiniteIdeal.emultiplicity_eq_multiplicity,
    ← hfiniteElement.emultiplicity_eq_multiplicity,
    Ideal.emultiplicity_eq_emultiplicity_span]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (a : BasePoint) (p : F256[X]) (hp : p ≠ 0) :
    (baseRationalPlace a).place.order
        (algebraMap F256[X] (RatFunc F256) p) =
      (p.rootMultiplicity (a : F256) : ℤ) := by
  change (GlobalPlace.rationalAdic (baseHeightOne a)).order
      (algebraMap F256[X] (RatFunc F256) p) = _
  unfold GlobalPlace.order GlobalPlace.rationalAdic
  rw [(baseHeightOne a).valuation_of_algebraMap,
    (baseHeightOne a).intValuation_eq_exp_neg_multiplicity hp,
    WithZero.log_exp]
  simp only [neg_neg]
  rw [baseHeightOne_asIdeal,
    basePolynomialIdealMultiplicity_eq_rootMultiplicity a p hp]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
