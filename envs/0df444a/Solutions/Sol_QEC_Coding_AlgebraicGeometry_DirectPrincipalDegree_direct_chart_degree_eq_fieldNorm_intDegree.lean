-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree.direct_chart_degree_eq_fieldNorm_intDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:25:44.922426+00:00
-- url     : https://prove2.me/submissions/9a54cdfe-d4fa-4668-b8e7-2712658d0848

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectPrincipalDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_affinePrincipalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_count_spanSingleton_eq_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residueDegree_eq_generator_natDegree_mul_inertia
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectNormCount_direct_intNorm_represents_fieldNorm
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectNormCount_direct_relNorm_spanSingleton_eq_intNorm
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectRelNormCoefficient_normalizedFactors_relNorm_eq_bind
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero


section
namespace QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree
open scoped BigOperators Polynomial RatFunc WithZero nonZeroDivisors
open UniqueFactorizationMonoid
open Submodule.IsPrincipal
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] directPrincipalDegree_constantAlgebra
attribute [local instance] directPrincipalDegree_isTorsionFree
private theorem factorPlaceOfPrime_asIdeal (P : Ideal (B k F)) (hP : Prime P) :
    (factorPlaceOfPrime k F P hP).asIdeal = P :=
  rfl
private theorem factorPlaceOfPrime_eq_iff (P : Ideal (B k F)) (hP : Prime P)
    (Q : AffinePlace.carrier k F) : factorPlaceOfPrime k F P hP = Q ↔ P = Q.asIdeal := by
  constructor
  · intro h
    simpa only [factorPlaceOfPrime_asIdeal] using congrArg
      IsDedekindDomain.HeightOneSpectrum.asIdeal h
  · intro h
    exact IsDedekindDomain.HeightOneSpectrum.ext
      (by simpa [factorPlaceOfPrime_asIdeal] using h)
private theorem factorDivisorOfPrimes_apply (s : Multiset (Ideal (B k F)))
    (hprime : ∀ P ∈ s, Prime P) (Q : AffinePlace.carrier k F) :
    factorDivisorOfPrimes k F s hprime Q = Multiset.count Q.asIdeal s := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [factorDivisorOfPrimes]
  | cons P m ih =>
      have hPprime : Prime P := hprime P (Multiset.mem_cons_self P m)
      let hmprime : ∀ q ∈ m, Prime q :=
        fun q hq => hprime q (Multiset.mem_cons_of_mem hq)
      have htail :
          ((m.attach.map fun q =>
            Finsupp.single
              (factorPlaceOfPrime k F q.1
                (hprime q.1 (Multiset.mem_cons_of_mem q.2))) (1 : Int)).sum) Q =
            Multiset.count Q.asIdeal m := by
        simpa only [factorDivisorOfPrimes] using ih hmprime
      rw [factorDivisorOfPrimes, Multiset.attach_cons, Multiset.map_cons,
        Multiset.map_map, Multiset.sum_cons, Finsupp.add_apply, Finsupp.single_apply,
        Multiset.count_cons]
      simp only [Function.comp_apply]
      rw [htail]
      by_cases hPQ : P = Q.asIdeal
      · have hplace : factorPlaceOfPrime k F P hPprime = Q :=
          (factorPlaceOfPrime_eq_iff k F P hPprime Q).mpr hPQ
        have hQP : Q.asIdeal = P := hPQ.symm
        simp only [if_pos hplace, if_pos hQP]
        exact Int.add_comm _ _
      · have hplace : factorPlaceOfPrime k F P hPprime ≠ Q := by
          intro h
          exact hPQ ((factorPlaceOfPrime_eq_iff k F P hPprime Q).mp h)
        have hQP : ¬Q.asIdeal = P := fun h => hPQ h.symm
        simp only [if_neg hplace, if_neg hQP, zero_add, Nat.add_zero]
private theorem factorDivisor_apply (I : Ideal (B k F))
    (Q : AffinePlace.carrier k F) :
    factorDivisor k F I Q = Multiset.count Q.asIdeal (normalizedFactors I) := by
  exact factorDivisorOfPrimes_apply k F (normalizedFactors I)
    (fun P hP => prime_of_normalized_factor P hP) Q
private theorem degree_factorDivisor (I : Ideal (B k F)) :
    Divisor.degree (AffinePlace.residueDegree k F) (factorDivisor k F I) =
      ((normalizedFactors I).attach.map fun P =>
        (AffinePlace.residueDegree k F (factorPlace k F I P) : Int)).sum := by
  classical
  unfold Divisor.degree Divisor.degreeHom factorDivisor factorDivisorOfPrimes
  rw [AddMonoidHom.map_multiset_sum]
  simp [Multiset.map_map, Function.comp_apply, factorPlace, factorPlaceOfPrime]
private theorem lower_factor_generator_degree (g : R k) (hg : g ≠ 0) :
    ((normalizedFactors (Ideal.span ({g} : Set (R k)))).map
      fun p => ((generator p).natDegree : Int)).sum = g.natDegree := by
  classical
  let m := normalizedFactors (Ideal.span ({g} : Set (R k)))
  let hprod : Ideal.span ({(m.map fun p => generator p).prod} : Set (R k)) =
      Ideal.span ({g} : Set (R k)) := by
    calc
      Ideal.span ({(m.map fun p => generator p).prod} : Set (R k)) =
          (m.map fun p => Ideal.span ({generator p} : Set (R k))).prod := by
        simpa only [Multiset.map_map, Function.comp_apply] using
          (Ideal.multiset_prod_span_singleton (m.map fun p => generator p)).symm
      _ = m.prod := by
        apply congrArg Multiset.prod
        have hmap :
            (m.map fun p => Ideal.span ({generator p} : Set (R k))) =
              m.map (fun p : Ideal (R k) => p) := by
          apply Multiset.map_congr rfl
          intro p hp
          exact Ideal.span_singleton_generator p
        simpa using hmap
      _ = Ideal.span ({g} : Set (R k)) :=
        Ideal.prod_normalizedFactors_eq_self (by
          exact mt Ideal.span_singleton_eq_bot.mp hg)
  have hassociated : Associated ((m.map fun p => generator p).prod) g := by
    exact Ideal.span_singleton_eq_span_singleton.mp hprod
  have hzero : (0 : R k) ∉ m.map fun p => generator p := by
    rintro h
    obtain ⟨p, hp, hpg⟩ := Multiset.mem_map.mp h
    have hpprime : Prime p := prime_of_normalized_factor p (by simpa [m] using hp)
    have hpne : p ≠ (0 : Ideal (R k)) := by
      simpa only [Ideal.zero_eq_bot] using hpprime.ne_zero
    exact hpne ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr hpg)
  rw [← Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated hassociated),
    Polynomial.natDegree_multiset_prod (m.map fun p => generator p) hzero,
    Nat.cast_multiset_sum]
  simp only [m, Multiset.map_map, Function.comp_apply]
private theorem factorDivisor_degree_eq_relNorm_generator_degree
    (I : Ideal (B k F)) (hI : I ≠ ⊥) :
    Divisor.degree (AffinePlace.residueDegree k F) (factorDivisor k F I) =
      ((normalizedFactors (Ideal.relNorm (R k) I)).map
        fun p => ((generator p).natDegree : Int)).sum := by
  classical
  rw [degree_factorDivisor]
  simp_rw [AffinePlace.residueDegree_eq_generator_natDegree_mul_inertia]
  change
    (Multiset.map
      (fun P : {P : Ideal (B k F) // P ∈ normalizedFactors I} =>
        (((generator (P.1.under (R k))).natDegree *
          (P.1.under (R k)).inertiaDeg' P.1 : Nat) : Int))
      (normalizedFactors I).attach).sum = _
  rw [Multiset.attach_map_val' (normalizedFactors I)
    (fun P => (((generator (P.under (R k))).natDegree *
      (P.under (R k)).inertiaDeg' P : Nat) : Int))]
  rw [_root_.QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.normalizedFactors_relNorm_eq_bind k F I hI]
  clear hI
  induction normalizedFactors I using Multiset.induction_on with
  | empty => simp
  | cons P m ih =>
      rw [Multiset.map_cons, Multiset.sum_cons,
        Multiset.cons_bind, Multiset.map_add, Multiset.sum_add,
        Multiset.map_replicate, Multiset.sum_replicate]
      rw [ih]
      norm_num
      ring
private theorem factorDivisor_degree_eq_intNorm_degree (x : B k F) (hx : x ≠ 0) :
    Divisor.degree (AffinePlace.residueDegree k F)
      (factorDivisor k F (Ideal.span ({x} : Set (B k F)))) =
      (Algebra.intNorm (R k) (B k F) x).natDegree := by
  have hspan : Ideal.span ({x} : Set (B k F)) ≠ ⊥ := by
    exact mt Ideal.span_singleton_eq_bot.mp hx
  rw [factorDivisor_degree_eq_relNorm_generator_degree k F
      (Ideal.span ({x} : Set (B k F))) hspan,
    DirectNormCount.direct_relNorm_spanSingleton_eq_intNorm]
  apply lower_factor_generator_degree k
  intro hnorm
  have hmapnorm : algebraMap (R k) k⟮X⟯
      (Algebra.intNorm (R k) (B k F) x) = 0 := by
    simpa only [hnorm, map_zero]
  rw [DirectNormCount.direct_intNorm_represents_fieldNorm] at hmapnorm
  have hxfield : algebraMap (B k F) F x ≠ 0 :=
    (map_ne_zero_iff (algebraMap (B k F) F)
      (IsFractionRing.injective (B k F) F)).mpr hx
  exact (Algebra.norm_ne_zero_iff.mpr hxfield) hmapnorm
private theorem affinePrincipalDivisor_sec_eq_sub (f : Fˣ) :
    let q := IsLocalization.sec (B k F)⁰ (f : F)
    AffinePlace.affinePrincipalDivisor k F f =
      factorDivisor k F (Ideal.span ({q.1} : Set (B k F))) -
        factorDivisor k F (Ideal.span ({(q.2 : B k F)} : Set (B k F))) := by
  classical
  let q := IsLocalization.sec (B k F)⁰ (f : F)
  have hqnum : q.1 ≠ 0 := IsLocalization.sec_fst_ne_zero f.ne_zero
  have hqden : (q.2 : B k F) ≠ 0 := nonZeroDivisors.coe_ne_zero q.2
  have hspan : FractionalIdeal.spanSingleton (B k F)⁰ (f : F) =
      FractionalIdeal.spanSingleton (B k F)⁰
          ((algebraMap (B k F) F) (q.2 : B k F))⁻¹ *
        (Ideal.span ({q.1} : Set (B k F))) := by
    have hq : IsLocalization.mk' F q.1 q.2 = (f : F) := by
      dsimp [q]
      exact IsLocalization.mk'_sec (M := (B k F)⁰) F (f : F)
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [← hq,
      IsFractionRing.mk'_eq_div,
      div_eq_mul_inv, mul_comm]
  have hfrac : FractionalIdeal.spanSingleton (B k F)⁰ (f : F) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr f.ne_zero
  have hqnumspan : Ideal.span ({q.1} : Set (B k F)) ≠ 0 :=
    mt Ideal.span_singleton_eq_bot.mp hqnum
  have hqdenspan : Ideal.span ({(q.2 : B k F)} : Set (B k F)) ≠ 0 :=
    mt Ideal.span_singleton_eq_bot.mp hqden
  ext P
  rw [AffinePlace.affinePrincipalDivisor_apply,
    ← AffinePlace.count_spanSingleton_eq_order k F P f.ne_zero,
    FractionalIdeal.count_well_defined F P hfrac hspan,
    Finsupp.sub_apply,
    factorDivisor_apply,
    factorDivisor_apply,
    Ideal.count_associates_factors_eq hqdenspan P.isPrime P.ne_bot,
    Ideal.count_associates_factors_eq hqnumspan P.isPrime P.ne_bot]
private theorem fieldNorm_sec_eq_intNorm_div (f : Fˣ) :
    let q := IsLocalization.sec (B k F)⁰ (f : F)
    Algebra.norm k⟮X⟯ (f : F) =
      algebraMap (R k) k⟮X⟯ (Algebra.intNorm (R k) (B k F) q.1) /
        algebraMap (R k) k⟮X⟯ (Algebra.intNorm (R k) (B k F) (q.2 : B k F)) := by
  let q := IsLocalization.sec (B k F)⁰ (f : F)
  have hq : IsLocalization.mk' F q.1 q.2 = (f : F) := by
    dsimp [q]
    exact IsLocalization.mk'_sec (M := (B k F)⁰) F (f : F)
  calc
    Algebra.norm k⟮X⟯ (f : F) =
        Algebra.norm k⟮X⟯ (IsLocalization.mk' F q.1 q.2) := by
      rw [hq]
    _ = Algebra.norm k⟮X⟯
        ((algebraMap (B k F) F) q.1 / (algebraMap (B k F) F) (q.2 : B k F)) := by
      rw [IsFractionRing.mk'_eq_div]
    _ = algebraMap (R k) k⟮X⟯ (Algebra.intNorm (R k) (B k F) q.1) /
        algebraMap (R k) k⟮X⟯
          (Algebra.intNorm (R k) (B k F) (q.2 : B k F)) := by
      rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
        ← DirectNormCount.direct_intNorm_represents_fieldNorm,
        ← DirectNormCount.direct_intNorm_represents_fieldNorm, div_eq_mul_inv]
end QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree
open scoped BigOperators Polynomial RatFunc WithZero nonZeroDivisors
open UniqueFactorizationMonoid
open Submodule.IsPrincipal
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree.directPrincipalDegree_constantAlgebra
attribute [local instance] directPrincipalDegree_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree.directPrincipalDegree_isTorsionFree
attribute [local instance] directPrincipalDegree_isTorsionFree
namespace QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree
theorem _root_.solution (f : Fˣ) :
    Divisor.degree (AffinePlace.residueDegree k F)
      (AffinePlace.affinePrincipalDivisor k F f) =
      (Algebra.norm k⟮X⟯ (f : F)).intDegree := by
  classical
  let q := IsLocalization.sec (B k F)⁰ (f : F)
  have hqnum : q.1 ≠ 0 := IsLocalization.sec_fst_ne_zero f.ne_zero
  have hqden : (q.2 : B k F) ≠ 0 := nonZeroDivisors.coe_ne_zero q.2
  have hnumMap : algebraMap (R k) k⟮X⟯
      (Algebra.intNorm (R k) (B k F) q.1) ≠ 0 := by
    rw [DirectNormCount.direct_intNorm_represents_fieldNorm]
    exact Algebra.norm_ne_zero_iff.mpr
      ((map_ne_zero_iff (algebraMap (B k F) F)
        (IsFractionRing.injective (B k F) F)).mpr hqnum)
  have hdenMap : algebraMap (R k) k⟮X⟯
      (Algebra.intNorm (R k) (B k F) (q.2 : B k F)) ≠ 0 := by
    rw [DirectNormCount.direct_intNorm_represents_fieldNorm]
    exact Algebra.norm_ne_zero_iff.mpr
      ((map_ne_zero_iff (algebraMap (B k F) F)
        (IsFractionRing.injective (B k F) F)).mpr hqden)
  rw [affinePrincipalDivisor_sec_eq_sub k F f, Divisor.degree_sub,
    factorDivisor_degree_eq_intNorm_degree k F q.1 hqnum,
    factorDivisor_degree_eq_intNorm_degree k F (q.2 : B k F) hqden,
    fieldNorm_sec_eq_intNorm_div k F f,
    RatFunc.intDegree_div hnumMap hdenMap,
    RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]
end QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree
