-- Prove2me | solution 1 for P2M_isUnramifiedAt_of_Separable_minpoly__f9724c9343b9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:15.497674+00:00
-- url     : https://prove2.me/submissions/a128c098-93e3-4bba-93f3-5a903bdf8ca4

module
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Unramified.Locus
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Theorems.Thm_algebraMap_injective_of_isIntegralClosure

set_option autoImplicit false
@[expose] public section
public section
open UniqueFactorizationMonoid Ideal
attribute [local instance] FractionRing.liftAlgebra
variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]
variable {R} {S}
open nonZeroDivisors Polynomial
attribute [local instance] Ideal.Quotient.field
theorem _root_.solution [Algebra.IsSeparable K L]
    (P : Ideal S) [hP : P.IsPrime] (hPbot : P ≠ ⊥) (x : S)
    (hx' : Algebra.adjoin K {algebraMap S L x} = ⊤)
    (h : Polynomial.Separable ((minpoly R x).map (Ideal.Quotient.mk (P.under R)))) :
    Algebra.IsUnramifiedAt R P := by
  classical
  have : IsDomain S := Function.Injective.isDomain _ (IsIntegralClosure.algebraMap_injective S R L)
  have hRS := algebraMap_injective_of_isIntegralClosure K L (R := R) (S := S)
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hRS
  have := IsIntegralClosure.isNoetherian R K L S
  have := IsIntegralClosure.isDedekindDomain R K L S
  have := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  have : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv R K).symm.toRingEquiv
      (FractionRing.algEquiv S L).symm.toRingEquiv (RingHom.ext fun x ↦
        IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
          (FractionRing.algEquiv S L).symm x)
  rw [← not_dvd_differentIdeal_iff (A := R) (B := S) (P := P)]
  intro hPdiv
  have hxP : aeval x (derivative (minpoly R x)) ∈ P :=
    (Ideal.dvd_iff_le.mp hPdiv) (aeval_derivative_mem_differentIdeal R K L _ hx')
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq] at hxP
  let p : Ideal R := P.under R
  have hpbot : p ≠ ⊥ := Ideal.under_ne_bot R hPbot
  have : p.IsMaximal := (show p.IsPrime from inferInstance).isMaximal hpbot
  have hle : p ≤ P.comap (algebraMap R S) := Localization.le_comap_primeCompl_iff.mp fun _ a ↦ a
  have hs := (separable_map (Ideal.quotientMap P (algebraMap R S) hle)).mpr h
  rw [Polynomial.map_map, Ideal.quotientMap_comp_mk] at hs
  apply hs.aeval_derivative_ne_zero (x := Ideal.Quotient.mk P x)
  · rw [← Polynomial.map_map]
    simp
  · rw [derivative_map, ← Polynomial.map_map]
    simpa [aeval_map_algebraMap] using hxP
