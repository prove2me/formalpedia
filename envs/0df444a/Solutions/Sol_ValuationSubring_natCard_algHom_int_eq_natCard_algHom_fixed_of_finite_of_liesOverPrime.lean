-- Prove2me | solution 1 for ValuationSubring.natCard_algHom_int_eq_natCard_algHom_fixed_of_finite_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/cc402f2d-7d37-55c7-807f-01f333d5970a

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Mathlib.FieldTheory.Galois.Infinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_natCard_algHom_int_eq_natCard_algHom_fixed_of_finite_of_liesOverPrime

set_option autoImplicit false

namespace GaloisFixedIntPoints

open ValuationSubring

theorem exists_ratCast_eq_of_fixed (y : AlgebraicClosure ℚ)
    (hy : ∀ σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ, σ y = y) :
    ∃ r : ℚ, (r : AlgebraicClosure ℚ) = y := by
  obtain ⟨r, hr⟩ :=
    (@InfiniteGalois.mem_range_algebraMap_iff_fixed ℚ (AlgebraicClosure ℚ) _ _
      (AlgebraicClosure.instAlgebra ℚ) _ y).mpr
      (fun f => hy (f : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
  exact ⟨r, (eq_ratCast _ r).symm.trans hr⟩

theorem not_dvd_den_of_mem (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ)
    (hA : A.LiesOverPrime p) (r : ℚ) (hr : (r : AlgebraicClosure ℚ) ∈ A) : ¬ p ∣ r.den := by
  rintro ⟨d, hd⟩
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact r.den_nz (by rw [hd, zero_mul])
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact r.den_nz (by rw [hd, mul_zero])
  have hp' : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hd' : (d : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0

  have hcop : Nat.Coprime r.num.natAbs p := Nat.Coprime.coprime_dvd_right ⟨d, hd⟩ r.reduced
  have hg : Int.gcd r.num p = 1 := by
    show r.num.natAbs.gcd (p : ℤ).natAbs = 1
    simpa using hcop
  have hbez : (1 : ℤ) = r.num * Int.gcdA r.num p + p * Int.gcdB r.num p := by
    have := Int.gcd_eq_gcd_ab r.num p
    rwa [hg, Nat.cast_one] at this

  have hmem1 : (r.num : AlgebraicClosure ℚ) / p ∈ A := by
    have : (r.num : AlgebraicClosure ℚ) / p = (r : AlgebraicClosure ℚ) * d := by
      rw [Rat.cast_def, hd]
      push_cast
      field_simp
    rw [this]
    exact mul_mem hr (natCast_mem A d)

  have hinv : (p : AlgebraicClosure ℚ)⁻¹ ∈ A := by
    have hbq : (1 : AlgebraicClosure ℚ)
        = r.num * (Int.gcdA r.num p : AlgebraicClosure ℚ) + p * Int.gcdB r.num p := by
      exact_mod_cast hbez
    have : (p : AlgebraicClosure ℚ)⁻¹
        = (Int.gcdA r.num p : AlgebraicClosure ℚ) * ((r.num : AlgebraicClosure ℚ) / p)
          + Int.gcdB r.num p := by
      field_simp
      linear_combination hbq
    rw [this]
    exact add_mem (mul_mem (intCast_mem A _) hmem1) (intCast_mem A _)

  have hlt : A.valuation (p : AlgebraicClosure ℚ) < 1 := (mem_nonunits_iff A).mp hA
  have hle : A.valuation (p : AlgebraicClosure ℚ)⁻¹ ≤ 1 := (valuation_le_one_iff A _).mpr hinv
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hp'))] at hle
  exact not_lt.mpr hle hlt

theorem not_dvd_den_of_finite (ℓ : ℕ) (hℓ : ℓ.Prime) (K : Type) [CommRing K] [Algebra ℤ K]
    (hfin : Module.Finite (GaloisRep.ratLocalizedAt ℓ)
      (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (ψ : K →ₐ[ℤ] ℚ) (x : K) : ¬ ℓ ∣ (ψ x).den := by

  obtain rfl : ‹Algebra ℤ K› = Ring.toIntAlgebra K := Subsingleton.elim _ _
  haveI : IsScalarTower ℤ (GaloisRep.ratLocalizedAt ℓ) ℚ :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI hprime : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hℓ)
  haveI : IsLocalization.AtPrime (GaloisRep.ratLocalizedAt ℓ) (Ideal.span {(ℓ : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt hℓ
  haveI := hfin

  let Φ : TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K →ₐ[GaloisRep.ratLocalizedAt ℓ] ℚ :=
    Algebra.TensorProduct.lift (Algebra.ofId (GaloisRep.ratLocalizedAt ℓ) ℚ) ψ
      (fun _ _ => Commute.all _ _)
  have hint : IsIntegral (GaloisRep.ratLocalizedAt ℓ) (ψ x) := by
    have h1 : IsIntegral (GaloisRep.ratLocalizedAt ℓ)
        ((1 : GaloisRep.ratLocalizedAt ℓ) ⊗ₜ[ℤ] x) := Algebra.IsIntegral.isIntegral _
    have h2 := h1.map Φ
    rwa [Algebra.TensorProduct.lift_tmul, map_one, one_mul] at h2
  obtain ⟨m, hm⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (Ideal.span {(ℓ : ℤ)}).primeCompl (ψ x)
      hint
  obtain ⟨n, hn⟩ := (isIntegrallyClosed_iff ℚ).mp (inferInstance : IsIntegrallyClosed ℤ) hm
  have hm0' : (m : ℤ) ≠ 0 := fun h => m.2 (by rw [h]; exact zero_mem _)
  have hm0 : ((m : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm0'
  have hn' : (n : ℚ) = (m : ℤ) * ψ x := by
    rw [← zsmul_eq_mul]
    exact (eq_intCast (algebraMap ℤ ℚ) n).symm.trans hn
  have hrq : ψ x = (n : ℚ) / (m : ℤ) := by
    rw [eq_div_iff hm0, mul_comm]
    exact hn'.symm
  intro hdvd
  have hden : ((ψ x).den : ℤ) ∣ (m : ℤ) := by
    have := Rat.den_dvd n m
    rwa [Rat.divInt_eq_div, ← hrq] at this
  exact m.2 (Ideal.mem_span_singleton.mpr ((Int.natCast_dvd_natCast.mpr hdvd).trans hden))

theorem natCard_algHom_int_eq (p : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) (K : Type) [CommRing K] [Algebra ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ)
        (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K)) :
    Nat.card (K →ₐ[ℤ] ℤ)
      = Nat.card {φ : K →ₐ[ℤ] ↥A //
          ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (x : K),
            σ (φ x : AlgebraicClosure ℚ) = (φ x : AlgebraicClosure ℚ)} := by

  have key : ∀ φ : K →ₐ[ℤ] ↥A,
      (∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (x : K),
        σ (φ x : AlgebraicClosure ℚ) = (φ x : AlgebraicClosure ℚ)) →
      ∀ x : K, ∃ n : ℤ, ((φ x : ↥A) : AlgebraicClosure ℚ) = n := by
    intro φ hφ

    have hrat : ∀ x : K, ∃ r : ℚ, (r : AlgebraicClosure ℚ) = φ x :=
      fun x => exists_ratCast_eq_of_fixed _ (fun σ => hφ σ x)
    choose rf hrf using hrat
    have rcast_inj : Function.Injective (fun r : ℚ => (r : AlgebraicClosure ℚ)) :=
      Rat.cast_injective
    let g : K →+* ℚ :=
      { toFun := rf
        map_one' := rcast_inj (by simp only; rw [hrf, map_one]; simp)
        map_mul' := fun a b => rcast_inj (by
          simp only; rw [Rat.cast_mul, hrf, hrf, hrf, map_mul]; simp)
        map_zero' := rcast_inj (by simp only; rw [hrf, map_zero]; simp)
        map_add' := fun a b => rcast_inj (by
          simp only; rw [Rat.cast_add, hrf, hrf, hrf, map_add]; simp) }
    let ψ : K →ₐ[ℤ] ℚ :=
      { g with
        commutes' := fun z => rcast_inj (by
          show ((rf (algebraMap ℤ K z) : ℚ) : AlgebraicClosure ℚ)
              = ((algebraMap ℤ ℚ z : ℚ) : AlgebraicClosure ℚ)
          rw [hrf, φ.commutes]
          simp) }
    intro x
    have hψx : ψ x = rf x := rfl
    have hden : (rf x).den = 1 := by
      refine Nat.eq_one_iff_not_exists_prime_dvd.mpr fun ℓ hℓ => ?_
      by_cases hℓp : ℓ = p
      · subst hℓp
        exact not_dvd_den_of_mem A ℓ hA (rf x) (by rw [hrf]; exact (φ x).2)
      · rw [← hψx]
        exact not_dvd_den_of_finite ℓ hℓ K (hff ℓ hℓ hℓp) ψ x
    refine ⟨(rf x).num, ?_⟩
    have hnum : ((rf x : ℚ) : AlgebraicClosure ℚ)
        = (((rf x).num : ℚ) : AlgebraicClosure ℚ) := by
      rw [Rat.coe_int_num_of_den_eq_one hden]
    rw [← hrf, hnum, Rat.cast_intCast]
  have cast_inj : Function.Injective (fun z : ℤ => (z : AlgebraicClosure ℚ)) := Int.cast_injective

  let F : (K →ₐ[ℤ] ℤ) →
      {φ : K →ₐ[ℤ] ↥A //
        ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (x : K),
          σ (φ x : AlgebraicClosure ℚ) = (φ x : AlgebraicClosure ℚ)} :=
    fun φ₀ => ⟨(Algebra.ofId ℤ ↥A).comp φ₀, fun σ x => by
      show σ (((algebraMap ℤ ↥A (φ₀ x) : ↥A)) : AlgebraicClosure ℚ) = _
      simp⟩
  refine Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)
  · intro φ₁ φ₂ h
    have h' := congrArg Subtype.val h
    ext x
    have hx := congrArg (fun ψ : K →ₐ[ℤ] ↥A => ((ψ x : ↥A) : AlgebraicClosure ℚ)) h'
    apply cast_inj
    simpa [F] using hx
  · rintro ⟨φ, hφ⟩
    choose n hn using key φ hφ
    let f : K →+* ℤ :=
      { toFun := n
        map_one' := cast_inj (by simp only; rw [← hn, map_one]; simp)
        map_mul' := fun a b => cast_inj (by simp only; rw [Int.cast_mul, ← hn, ← hn, ← hn, map_mul]; simp)
        map_zero' := cast_inj (by simp only; rw [← hn, map_zero]; simp)
        map_add' := fun a b => cast_inj (by simp only; rw [Int.cast_add, ← hn, ← hn, ← hn, map_add]; simp) }
    let φ₀ : K →ₐ[ℤ] ℤ :=
      { f with
        commutes' := fun z => cast_inj (by
          show ((n (algebraMap ℤ K z) : ℤ) : AlgebraicClosure ℚ)
              = ((algebraMap ℤ ℤ z : ℤ) : AlgebraicClosure ℚ)
          rw [← hn, φ.commutes]
          simp) }
    refine ⟨φ₀, Subtype.ext ?_⟩
    ext x
    show ((algebraMap ℤ ↥A (n x) : ↥A) : AlgebraicClosure ℚ) = (φ x : AlgebraicClosure ℚ)
    rw [hn]
    simp

end GaloisFixedIntPoints

theorem solution
    (p : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (K : Type) [CommRing K] [Algebra ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ)
        (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K)) :
    Nat.card (K →ₐ[ℤ] ℤ)
      = Nat.card {φ : K →ₐ[ℤ] ↥A //
          ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (x : K),
            σ (φ x : AlgebraicClosure ℚ) = (φ x : AlgebraicClosure ℚ)} :=
  GaloisFixedIntPoints.natCard_algHom_int_eq p A hA K hff

end S_ValuationSubring_natCard_algHom_int_eq_natCard_algHom_fixed_of_finite_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_natCard_algHom_int_eq_natCard_algHom_fixed_of_finite_of_liesOverPrime (solution)
