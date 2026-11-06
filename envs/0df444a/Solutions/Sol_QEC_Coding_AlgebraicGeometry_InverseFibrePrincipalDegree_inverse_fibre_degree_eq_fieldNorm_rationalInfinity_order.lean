-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree.inverse_fibre_degree_eq_fieldNorm_rationalInfinity_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:27:37.889984+00:00
-- url     : https://prove2.me/submissions/2c018439-34b6-488b-ae69-25067b1a6b17

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_InverseFibrePrincipalDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_affinePrincipalCoefficient_eq_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residueDegree_eq_generator_natDegree_mul_inertia
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectNormCount_direct_intNorm_represents_fieldNorm
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectRelNormCoefficient_direct_intNorm_span_coefficient_eq_sum_primesOver
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_infinityFibrePrincipalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_transported_norm_xAdic_to_original_infinity
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


section
namespace QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree
open scoped BigOperators Polynomial RatFunc WithZero nonZeroDivisors
open UniqueFactorizationMonoid
open Submodule.IsPrincipal
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
local notation3 "R" => k[X]
local notation3 "B" => inverseRingOfIntegers
  (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
  (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
  (oldSeparable := oldSeparable) k F
attribute [local instance] inverseFibrePrincipalDegree_isTorsionFree
private theorem inverseFibrePrincipalDivisor_apply
    (f : Fˣ) (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    inverseFibrePrincipalDivisor
      (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F f D =
      GlobalPlace.order (InverseAffinePlace.globalPlace
        (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
        (oldSeparable := oldSeparable) k F D) (f : F) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  exact InverseAffinePlace.infinityFibrePrincipalDivisor_apply
    (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra) (τ := oldScalarTower)
    (φ := oldFunctionField) (σ := oldSeparable) (k := k) (F := F) f D
private theorem xPrime_ne_bot : xPrime k ≠ ⊥ :=
  by
    simpa only [xPrime, InverseAffinePlace.infinityBasePrime] using
      (Polynomial.idealX k).ne_bot
private theorem xPrime_generator_natDegree :
    ((generator (xPrime k)).natDegree : Int) = 1 := by
  have hspan : Ideal.span ({generator (xPrime k)} : Set R) =
      Ideal.span ({Polynomial.X} : Set R) := by
    rw [Ideal.span_singleton_generator (xPrime k)]
    rfl
  have hassociated : Associated (generator (xPrime k)) (Polynomial.X : R) :=
    Ideal.span_singleton_eq_span_singleton.mp hspan
  have hnat : (generator (xPrime k)).natDegree = (Polynomial.X : R).natDegree :=
    Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated hassociated)
  calc
    ((generator (xPrime k)).natDegree : Int) = ((Polynomial.X : R).natDegree : Int) := by
      exact_mod_cast hnat
    _ = 1 := by simp
private theorem inverseFibre_order_eq_sec_counts
    (f : Fˣ) (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    let q := IsLocalization.sec B⁰ (f : F)
    GlobalPlace.order (InverseAffinePlace.globalPlace
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F D) (f : F) =
      Multiset.count D.1.asIdeal
        (normalizedFactors (Ideal.span ({q.1} : Set B))) -
      Multiset.count D.1.asIdeal
        (normalizedFactors (Ideal.span ({(q.2 : B)} : Set B))) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  let q := IsLocalization.sec B⁰ (f : F)
  have hnum : q.1 ≠ 0 := IsLocalization.sec_fst_ne_zero f.ne_zero
  have hden : (q.2 : B) ≠ 0 := nonZeroDivisors.coe_ne_zero q.2
  have hnumspan : Ideal.span ({q.1} : Set B) ≠ (0 : Ideal B) := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hnum
  have hdenspan : Ideal.span ({(q.2 : B)} : Set B) ≠ (0 : Ideal B) := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hden
  change GlobalPlace.order (AffinePlace.globalPlace k F D.1) (f : F) = _
  rw [← AffinePlace.affinePrincipalCoefficient_eq_order k F D.1 f]
  unfold AffinePlace.affinePrincipalCoefficient
  unfold IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero
  unfold IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroToFun
  change -(-((Associates.mk D.1.asIdeal).count
      (Associates.mk (Ideal.span ({q.1} : Set B))).factors : ℤ) -
    -((Associates.mk D.1.asIdeal).count
      (Associates.mk (Ideal.span ({(q.2 : B)} : Set B))).factors : ℤ)) = _
  rw [Ideal.count_associates_factors_eq,
    Ideal.count_associates_factors_eq]
  · ring
  · exact hdenspan
  · exact D.1.isPrime
  · exact D.1.ne_bot
  · exact hnumspan
  · exact D.1.isPrime
  · exact D.1.ne_bot
private theorem fibre_sum_eq_primesOver_sum (g : Ideal B -> Int) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
    ∑ D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := oldRationalAlgebra) k F,
      g D.1.asIdeal =
      ∑ P ∈ IsDedekindDomain.primesOverFinset (xPrime k) B, g P := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
  letI : Fintype (InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :=
    InverseAffinePlace.infinityFibreFintype (oldRationalAlgebra := oldRationalAlgebra) k F
  let e := InverseAffinePlace.infinityFibreEquivPrimesOver
    (oldRationalAlgebra := oldRationalAlgebra) k F
  let hs : (↑(IsDedekindDomain.primesOverFinset (xPrime k) B) : Set (Ideal B)) =
      (xPrime k).primesOver B :=
    IsDedekindDomain.coe_primesOverFinset (xPrime_ne_bot k) B
  letI : Fintype ((xPrime k).primesOver B) :=
    Fintype.ofEquiv
      (InverseAffinePlace.infinityFibre (oldRationalAlgebra := oldRationalAlgebra) k F) e
  let e' := e.trans (Equiv.setCongr hs.symm)
  calc
    ∑ D : InverseAffinePlace.infinityFibre
        (oldRationalAlgebra := oldRationalAlgebra) k F, g D.1.asIdeal =
        ∑ P : IsDedekindDomain.primesOverFinset (xPrime k) B, g P := by
      exact e'.sum_comp (fun P => g P)
    _ = ∑ P ∈ IsDedekindDomain.primesOverFinset (xPrime k) B, g P :=
      Finset.sum_coe_sort _ _
private theorem fibre_integral_degree_eq_X_norm_count
    (x : B) (hx : x ≠ 0) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
    ∑ D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := oldRationalAlgebra) k F,
      (inverseFibreResidueDegree
        (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
        (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
        (oldSeparable := oldSeparable) k F D : Int) *
        Multiset.count D.1.asIdeal
          (normalizedFactors (Ideal.span ({x} : Set B))) =
      Multiset.count (xPrime k)
        (normalizedFactors (Ideal.span
          ({Algebra.intNorm R B x} : Set R))) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
  letI : Module.IsTorsionFree R F :=
    Module.IsTorsionFree.trans_faithfulSMul R k⟮X⟯ F
  letI : Module.IsTorsionFree R B := IsIntegralClosure.isTorsionFree R F
  let e := InverseAffinePlace.infinityFibreEquivPrimesOver
    (oldRationalAlgebra := oldRationalAlgebra) k F
  have hbase (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
      AffinePlace.basePrime k F D.1 = xPrime k := by
    change D.1.asIdeal.under R = xPrime k
    exact (e D).2.2.over.symm
  have hres (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
      inverseFibreResidueDegree
        (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
        (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
        (oldSeparable := oldSeparable) k F D =
        AffinePlace.residueDegree k F D.1 := rfl
  simp_rw [hres,
    AffinePlace.residueDegree_eq_generator_natDegree_mul_inertia,
    hbase, Nat.cast_mul, xPrime_generator_natDegree]
  simp only [one_mul]
  rw [fibre_sum_eq_primesOver_sum
    (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
    (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
    (oldSeparable := oldSeparable) k F
      (fun P => ((xPrime k).inertiaDeg' P : Int) *
        (Multiset.count P (normalizedFactors (Ideal.span ({x} : Set B))) : Int))]
  exact_mod_cast (_root_.QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.direct_intNorm_span_coefficient_eq_sum_primesOver k F x hx
      (xPrime k) (xPrime_ne_bot k)).symm
private theorem xPrime_count_eq_natTrailingDegree
    (p : R) (hp : p ≠ 0) :
    Multiset.count (xPrime k)
      (normalizedFactors (Ideal.span ({p} : Set R))) = p.natTrailingDegree := by
  classical
  letI : StrongNormalizationMonoid k := UniqueFactorizationMonoid.strongNormalizationMonoid
  rw [xPrime, InverseAffinePlace.infinityBasePrime, Polynomial.idealX_span,
    Ideal.count_span_normalizedFactors_eq_of_normUnit hp
      Polynomial.normUnit_X Polynomial.prime_X]
  rw [← Polynomial.rootMultiplicity_eq_natTrailingDegree',
    Polynomial.rootMultiplicity_eq_multiplicity, if_neg hp]
  have hX : (Polynomial.X - Polynomial.C (0 : k) : R) = Polynomial.X := by
    simp
  rw [hX]
  symm
  simpa only [← Polynomial.X_eq_normalize] using
    (UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
      Polynomial.irreducible_X hp)
private theorem xAdic_order_polynomial (p : R) (hp : p ≠ 0) :
    GlobalPlace.order (InverseRationalInfinityTransport.xAdicPlace k)
      (algebraMap R k⟮X⟯ p) = (p.natTrailingDegree : Int) := by
  classical
  letI : StrongNormalizationMonoid k := UniqueFactorizationMonoid.strongNormalizationMonoid
  unfold InverseRationalInfinityTransport.xAdicPlace GlobalPlace.order
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg]
  · rw [WithZero.log_exp]
    simp only [neg_neg]
    congr 1
    rw [Ideal.count_associates_factors_eq
      (by simpa [Ideal.zero_eq_bot] using hp)
      (Polynomial.idealX k).isPrime (Polynomial.idealX k).ne_bot]
    rw [Polynomial.idealX_span,
      Ideal.count_span_normalizedFactors_eq_of_normUnit hp
        Polynomial.normUnit_X Polynomial.prime_X]
    rw [← Polynomial.rootMultiplicity_eq_natTrailingDegree',
      Polynomial.rootMultiplicity_eq_multiplicity, if_neg hp]
    have hX : (Polynomial.X - Polynomial.C (0 : k) : R) = Polynomial.X := by
      simp
    rw [hX]
    symm
    simpa only [← Polynomial.X_eq_normalize] using
      (UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
        Polynomial.irreducible_X hp)
  · exact hp
private theorem X_norm_count_eq_xAdic_order_integral
    (x : B) (hx : x ≠ 0) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
    Multiset.count (xPrime k)
      (normalizedFactors (Ideal.span
        ({Algebra.intNorm R B x} : Set R))) =
      GlobalPlace.order (InverseRationalInfinityTransport.xAdicPlace k)
        (Algebra.norm k⟮X⟯ (algebraMap B F x)) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
  letI : Module.IsTorsionFree R F :=
    Module.IsTorsionFree.trans_faithfulSMul R k⟮X⟯ F
  letI : Module.IsTorsionFree R B := IsIntegralClosure.isTorsionFree R F
  let hfield : algebraMap B F x ≠ 0 :=
    (map_ne_zero_iff (algebraMap B F) (IsFractionRing.injective B F)).mpr hx
  have hnorm : Algebra.intNorm R B x ≠ 0 := by
    intro hzero
    have hmapnorm : algebraMap R k⟮X⟯ (Algebra.intNorm R B x) = 0 := by
      simpa only [hzero, map_zero]
    rw [DirectNormCount.direct_intNorm_represents_fieldNorm] at hmapnorm
    exact (Algebra.norm_ne_zero_iff.mpr hfield) hmapnorm
  rw [xPrime_count_eq_natTrailingDegree k _ hnorm]
  calc
    ((Algebra.intNorm R B x).natTrailingDegree : Int) =
        GlobalPlace.order (InverseRationalInfinityTransport.xAdicPlace k)
          (algebraMap R k⟮X⟯ (Algebra.intNorm R B x)) :=
      (xAdic_order_polynomial k (Algebra.intNorm R B x) hnorm).symm
    _ = GlobalPlace.order (InverseRationalInfinityTransport.xAdicPlace k)
        (Algebra.norm k⟮X⟯ (algebraMap B F x)) := by
      rw [DirectNormCount.direct_intNorm_represents_fieldNorm]
private theorem transported_norm_sec_eq_intNorm_div (f : Fˣ) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
    let q := IsLocalization.sec B⁰ (f : F)
    Algebra.norm k⟮X⟯ (f : F) =
      algebraMap R k⟮X⟯ (Algebra.intNorm R B q.1) /
      algebraMap R k⟮X⟯ (Algebra.intNorm R B (q.2 : B)) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
  letI : Module.IsTorsionFree R F :=
    Module.IsTorsionFree.trans_faithfulSMul R k⟮X⟯ F
  letI : Module.IsTorsionFree R B := IsIntegralClosure.isTorsionFree R F
  let q := IsLocalization.sec B⁰ (f : F)
  have hq : IsLocalization.mk' F q.1 q.2 = (f : F) := by
    dsimp [q]
    exact IsLocalization.mk'_sec (M := B⁰) F (f : F)
  calc
    Algebra.norm k⟮X⟯ (f : F) =
        Algebra.norm k⟮X⟯ (IsLocalization.mk' F q.1 q.2) := by
      rw [hq]
    _ = Algebra.norm k⟮X⟯
        ((algebraMap B F) q.1 / (algebraMap B F) (q.2 : B)) := by
      rw [IsFractionRing.mk'_eq_div]
    _ = algebraMap R k⟮X⟯ (Algebra.intNorm R B q.1) /
        algebraMap R k⟮X⟯ (Algebra.intNorm R B (q.2 : B)) := by
      rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
        ← DirectNormCount.direct_intNorm_represents_fieldNorm,
        ← DirectNormCount.direct_intNorm_represents_fieldNorm, div_eq_mul_inv]
private theorem fibre_degree_eq_transported_norm_xAdic_order (f : Fˣ) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := oldRationalAlgebra) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
    Divisor.degree (inverseFibreResidueDegree
      (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F)
      (inverseFibrePrincipalDivisor
        (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
        (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
        (oldSeparable := oldSeparable) k F f) =
      GlobalPlace.order (InverseRationalInfinityTransport.xAdicPlace k)
        (Algebra.norm k⟮X⟯ (f : F)) := by
  classical
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
  letI : Module.IsTorsionFree R F :=
    Module.IsTorsionFree.trans_faithfulSMul R k⟮X⟯ F
  letI : Module.IsTorsionFree R B := IsIntegralClosure.isTorsionFree R F
  letI : Fintype (InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :=
    InverseAffinePlace.infinityFibreFintype (oldRationalAlgebra := oldRationalAlgebra) k F
  let q := IsLocalization.sec B⁰ (f : F)
  have hnum : q.1 ≠ 0 := IsLocalization.sec_fst_ne_zero f.ne_zero
  have hden : (q.2 : B) ≠ 0 := nonZeroDivisors.coe_ne_zero q.2
  change (inverseFibrePrincipalDivisor
      (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F f).sum
      (fun D c => c * (inverseFibreResidueDegree
        (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
        (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
        (oldSeparable := oldSeparable) k F D : Int)) = _
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp_rw [inverseFibrePrincipalDivisor_apply
    (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
    (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
    (oldSeparable := oldSeparable)]
  simp_rw [inverseFibre_order_eq_sec_counts
    (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
    (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
    (oldSeparable := oldSeparable)]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hnum_mul :
      (∑ D : InverseAffinePlace.infinityFibre
          (oldRationalAlgebra := oldRationalAlgebra) k F,
        (Multiset.count D.1.asIdeal
          (normalizedFactors (Ideal.span ({q.1} : Set B))) : Int) *
          (inverseFibreResidueDegree
            (oldPolynomialAlgebra := oldPolynomialAlgebra)
            (oldRationalAlgebra := oldRationalAlgebra) (oldScalarTower := oldScalarTower)
            (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable) k F D : Int)) =
        ∑ D : InverseAffinePlace.infinityFibre
          (oldRationalAlgebra := oldRationalAlgebra) k F,
          (inverseFibreResidueDegree
            (oldPolynomialAlgebra := oldPolynomialAlgebra)
            (oldRationalAlgebra := oldRationalAlgebra) (oldScalarTower := oldScalarTower)
            (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable) k F D : Int) *
          Multiset.count D.1.asIdeal
            (normalizedFactors (Ideal.span ({q.1} : Set B))) := by
    apply Finset.sum_congr rfl
    intro D _
    ring
  have hden_mul :
      (∑ D : InverseAffinePlace.infinityFibre
          (oldRationalAlgebra := oldRationalAlgebra) k F,
        (Multiset.count D.1.asIdeal
          (normalizedFactors (Ideal.span ({(q.2 : B)} : Set B))) : Int) *
          (inverseFibreResidueDegree
            (oldPolynomialAlgebra := oldPolynomialAlgebra)
            (oldRationalAlgebra := oldRationalAlgebra) (oldScalarTower := oldScalarTower)
            (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable) k F D : Int)) =
        ∑ D : InverseAffinePlace.infinityFibre
          (oldRationalAlgebra := oldRationalAlgebra) k F,
          (inverseFibreResidueDegree
            (oldPolynomialAlgebra := oldPolynomialAlgebra)
            (oldRationalAlgebra := oldRationalAlgebra) (oldScalarTower := oldScalarTower)
            (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable) k F D : Int) *
          Multiset.count D.1.asIdeal
            (normalizedFactors (Ideal.span ({(q.2 : B)} : Set B))) := by
    apply Finset.sum_congr rfl
    intro D _
    ring
  rw [hnum_mul, hden_mul]
  change
    (∑ D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := oldRationalAlgebra) k F,
      (inverseFibreResidueDegree
        (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
        (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
        (oldSeparable := oldSeparable) k F D : Int) *
        Multiset.count D.1.asIdeal
          (normalizedFactors (Ideal.span ({q.1} : Set B)))) -
      (∑ D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := oldRationalAlgebra) k F,
      (inverseFibreResidueDegree
        (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
        (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
        (oldSeparable := oldSeparable) k F D : Int) *
        Multiset.count D.1.asIdeal
            (normalizedFactors (Ideal.span ({(q.2 : B)} : Set B)))) = _
  rw [fibre_integral_degree_eq_X_norm_count
      (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F q.1 hnum,
    fibre_integral_degree_eq_X_norm_count
      (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F (q.2 : B) hden,
    X_norm_count_eq_xAdic_order_integral
      (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F q.1 hnum,
    X_norm_count_eq_xAdic_order_integral
      (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F (q.2 : B) hden,
    transported_norm_sec_eq_intNorm_div
      (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable)]
  have hnumfield : algebraMap B F q.1 ≠ 0 :=
    (map_ne_zero_iff (algebraMap B F) (IsFractionRing.injective B F)).mpr hnum
  have hdenfield : algebraMap B F (q.2 : B) ≠ 0 :=
    (map_ne_zero_iff (algebraMap B F) (IsFractionRing.injective B F)).mpr hden
  have hnumNorm : Algebra.norm k⟮X⟯ (algebraMap B F q.1) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hnumfield
  have hdenNorm : Algebra.norm k⟮X⟯ (algebraMap B F (q.2 : B)) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hdenfield
  rw [DirectNormCount.direct_intNorm_represents_fieldNorm,
    DirectNormCount.direct_intNorm_represents_fieldNorm,
    div_eq_mul_inv, GlobalPlace.order_mul]
  · rw [GlobalPlace.order_inv]
    ring
  · exact hnumNorm
  · exact inv_ne_zero hdenNorm
end QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree
open scoped BigOperators Polynomial RatFunc WithZero nonZeroDivisors
open UniqueFactorizationMonoid
open Submodule.IsPrincipal
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
local notation3 "R" => k[X]
local notation3 "B" => inverseRingOfIntegers
  (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
  (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
  (oldSeparable := oldSeparable) k F
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree.inverseFibrePrincipalDegree_isTorsionFree
attribute [local instance] inverseFibrePrincipalDegree_isTorsionFree
namespace QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree
theorem _root_.solution (f : Fˣ) :
    Divisor.degree (inverseFibreResidueDegree
      (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F)
      (inverseFibrePrincipalDivisor
        (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
        (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
        (oldSeparable := oldSeparable) k F f) =
      GlobalPlace.order (GlobalPlace.rationalInfinity k)
        (@Algebra.norm k⟮X⟯ F _ _ oldRationalAlgebra (f : F)) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
  rw [fibre_degree_eq_transported_norm_xAdic_order
    (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
    (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
    (oldSeparable := oldSeparable) k F]
  exact _root_.QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.transported_norm_xAdic_to_original_infinity
    (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
    (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
    (oldSeparable := oldSeparable) k F (f : F)
end QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree
