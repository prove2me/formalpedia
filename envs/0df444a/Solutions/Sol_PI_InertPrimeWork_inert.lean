-- Prove2me | solution 1 for PI.InertPrimeWork.inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:48.499298+00:00
-- url     : https://prove2.me/submissions/af71f0ac-9761-4185-acc6-b53500343c4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InertPrime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeJacobi_NotIsSquareOfJacobi
import Theorems.Thm_PI_InertPrimeWork_not_isSquare_of_jacobi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.InertPrimeWork
namespace PI.InertPrimeWork
theorem _root_.solution (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (b : K) (d p : ℕ)
    (hb : b ^ 2 = -(d : K)) (hp : p.Prime) (hj : jacobiSym (-(d : ℤ)) p = -1) :
    (Ideal.span {(p : 𝓞 K)}).IsPrime := by
  haveI := Fact.mk hp
  have hsq := not_isSquare_of_jacobi hp hj
  have hnormI : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_singleton]
    have e : ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hK]
    simp
  have hp1 : p ^ 2 ≠ 1 := by
    have := hp.one_lt
    nlinarith
  have hIne : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at hnormI
    exact hp1 hnormI.symm
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal _ hIne
  have hdvd : Ideal.absNorm P ∣ p ^ 2 := hnormI ▸ Ideal.absNorm_dvd_absNorm_of_le hIP
  obtain ⟨k, hk, hPk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  interval_cases k
  · rw [pow_zero, Ideal.absNorm_eq_one_iff] at hPk
    exact absurd hPk hPmax.ne_top
  · exfalso
    rw [pow_one] at hPk
    have hP0 : P ≠ ⊥ := by
      rintro rfl
      rw [Ideal.absNorm_bot] at hPk
      exact hp.ne_zero hPk.symm
    haveI : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
    letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    have hcard : Fintype.card (𝓞 K ⧸ P) = p := by
      rw [Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hPk]
    haveI : CharP (𝓞 K ⧸ P) p := charP_of_card_eq_prime hcard
    let ψ : ZMod p →+* 𝓞 K ⧸ P := ZMod.castHom (dvd_refl p) _
    have hψi : Function.Injective ψ := ψ.injective
    have hψb : Function.Bijective ψ :=
      (Fintype.bijective_iff_injective_and_card ψ).2 ⟨hψi, by rw [ZMod.card, hcard]⟩
    have hbi : IsIntegral ℤ b := by
      refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
      · exact Polynomial.monic_X_pow_add_C _ two_ne_zero
      · simp [Polynomial.eval₂_add, hb]
    let β : 𝓞 K := ⟨b, hbi⟩
    have hβ : β ^ 2 = -(d : 𝓞 K) := by
      apply RingOfIntegers.coe_injective
      push_cast
      exact hb
    obtain ⟨t, ht⟩ := hψb.2 (Ideal.Quotient.mk P β)
    apply hsq
    refine ⟨t, ?_⟩
    apply hψi
    rw [map_mul, ← sq, ht, ← map_pow, hβ]
    push_cast
    simp
  · rw [← hnormI] at hPk
    have hPI : P ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_iff_le.2 hIP
    obtain ⟨J, hJ⟩ := hPI
    have hJ1 : Ideal.absNorm J = 1 := by
      have h2 := congrArg Ideal.absNorm hJ
      rw [map_mul, hPk] at h2
      have hpos : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) ≠ 0 := by
        rw [hnormI]
        exact pow_ne_zero _ hp.ne_zero
      exact (Nat.mul_eq_left hpos).1 h2.symm
    rw [Ideal.absNorm_eq_one_iff] at hJ1
    rw [hJ, hJ1, Ideal.mul_top]
    exact hPmax.isPrime
end PI.InertPrimeWork
