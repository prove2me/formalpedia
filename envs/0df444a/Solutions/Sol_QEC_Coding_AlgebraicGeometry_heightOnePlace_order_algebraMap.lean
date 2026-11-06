-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.heightOnePlace_order_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:32:05.91951+00:00
-- url     : https://prove2.me/submissions/9aa0ac55-8327-48a8-a1a8-3f68534d45ff

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_integral
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul

section
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]
private theorem heightOne_multiplicity_map
    {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra R S] [FaithfulSMul R S]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (I : Ideal R) (hI : I ≠ ⊥) :
    multiplicity J.asIdeal (Ideal.map (algebraMap R S) I) =
      H.asIdeal.ramificationIdx' J.asIdeal * multiplicity H.asIdeal I := by
  have hH : Prime H.asIdeal := Ideal.prime_of_isPrime H.ne_bot H.isPrime
  have hJ : Prime J.asIdeal := Ideal.prime_of_isPrime J.ne_bot J.isPrime
  have hmap : Ideal.map (algebraMap R S) I ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI
  have hIfin : FiniteMultiplicity H.asIdeal I := FiniteMultiplicity.of_prime_left hH hI
  have hJfin : FiniteMultiplicity J.asIdeal (Ideal.map (algebraMap R S) I) :=
    FiniteMultiplicity.of_prime_left hJ hmap
  have h := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
    hI hH.irreducible hJ.irreducible J.ne_bot
  rw [hIfin.emultiplicity_eq_multiplicity, hJfin.emultiplicity_eq_multiplicity] at h
  exact_mod_cast h
private theorem place_order_div
    {K : Type*} [Field K] [Algebra k K] (P : GlobalPlace k K)
    {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    P.order (r / s) = P.order r - P.order s := by
  rw [div_eq_mul_inv, P.order_mul hr (inv_ne_zero hs), P.order_inv, sub_eq_add_neg]
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra k K] [Algebra k L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra R S] [FaithfulSMul R S] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (x : K) (hx : x ≠ 0) :
    (heightOnePlace (k := k) (K := L) J).order (algebraMap K L x) =
      (H.asIdeal.ramificationIdx' J.asIdeal : ℤ) *
        (heightOnePlace (k := k) (K := K) H).order x := by
  let P := heightOnePlace (k := k) (K := K) H
  let Q := heightOnePlace (k := k) (K := L) J
  have hi (r : R) (hr : r ≠ 0) :
      Q.order (algebraMap K L (algebraMap R K r)) =
        (H.asIdeal.ramificationIdx' J.asIdeal : ℤ) * P.order (algebraMap R K r) := by
    have hmapr : algebraMap R S r ≠ 0 := by
      simpa only [map_zero] using (FaithfulSMul.algebraMap_injective R S).ne hr
    have hspan : Ideal.span ({r} : Set R) ≠ ⊥ := by
      simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hr
    have hm := heightOne_multiplicity_map H J (Ideal.span {r}) hspan
    rw [Ideal.map_span, Set.image_singleton] at hm
    rw [← IsScalarTower.algebraMap_apply R K L,
      IsScalarTower.algebraMap_apply R S L]
    change (heightOnePlace (k := k) (K := L) J).order
        (algebraMap S L (algebraMap R S r)) =
      (H.asIdeal.ramificationIdx' J.asIdeal : ℤ) *
        (heightOnePlace (k := k) (K := K) H).order (algebraMap R K r)
    rw [heightOnePlace_order_integral J hmapr, heightOnePlace_order_integral H hr, hm]
    exact Nat.cast_mul _ _
  obtain ⟨r, s, hs, hfrac⟩ := IsFractionRing.div_surjective R x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    intro h
    apply hx
    rw [← hfrac, h, map_zero, zero_div]
  have hrK : algebraMap R K r ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hr0
  have hsK : algebraMap R K s ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hs0
  have hrL : algebraMap K L (algebraMap R K r) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne hrK
  have hsL : algebraMap K L (algebraMap R K s) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne hsK
  change Q.order (algebraMap K L x) = (H.asIdeal.ramificationIdx' J.asIdeal : ℤ) * P.order x
  rw [← hfrac, map_div₀, place_order_div Q hrL hsL, place_order_div P hrK hsK,
    hi r hr0, hi s hs0]
  ring
end QEC.Coding.AlgebraicGeometry
