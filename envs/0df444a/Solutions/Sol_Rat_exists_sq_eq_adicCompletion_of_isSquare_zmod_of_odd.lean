-- Prove2me | solution 1 for Rat.exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/916f9b8b-6014-5b6e-8164-42a228cf5e75

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rat_exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd

set_option autoImplicit false

open IsDedekindDomain NumberField Polynomial

namespace HenselOddChi

theorem exists_sq_eq_padicInt (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u)
    (hsq : IsSquare (u : ZMod p)) : ∃ z : ℤ_[p], z ^ 2 = (u : ℤ_[p]) := by

  obtain ⟨tbar, htbar⟩ := hsq
  obtain ⟨t, rfl⟩ := ZMod.intCast_surjective tbar
  have hdvd : (p : ℤ) ∣ t * t - u := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [← htbar]; ring
  have hpt : ¬ (p : ℤ) ∣ t := by
    intro h
    apply hu
    have htt : (p : ℤ) ∣ t * t := dvd_mul_of_dvd_left h t
    have : u = t * t - (t * t - u) := by ring
    rw [this]
    exact dvd_sub htt hdvd
  let F : Polynomial ℤ := X ^ 2 - C u
  have hF : ∀ a : ℤ_[p], F.aeval a = a ^ 2 - (u : ℤ_[p]) := by intro a; simp [F]
  have hF' : ∀ a : ℤ_[p], F.derivative.aeval a = 2 * a := by
    intro a
    have hd : F.derivative = C (2 : ℤ) * X := by
      simp only [F, derivative_sub, derivative_X_pow, derivative_C, sub_zero, Nat.cast_ofNat, pow_one]
      norm_num
    rw [hd, map_mul, aeval_C, aeval_X, eq_intCast]
    push_cast
    rfl
  have hnorm : ‖F.aeval (t : ℤ_[p])‖ < ‖F.derivative.aeval (t : ℤ_[p])‖ ^ 2 := by
    rw [hF, hF']
    have h1 : ‖(t : ℤ_[p]) ^ 2 - (u : ℤ_[p])‖ < 1 := by
      have : ((t : ℤ_[p]) ^ 2 - (u : ℤ_[p])) = ((t * t - u : ℤ) : ℤ_[p]) := by push_cast; ring
      rw [this, PadicInt.norm_int_lt_one_iff_dvd]
      exact hdvd
    have h2 : ‖(2 : ℤ_[p]) * (t : ℤ_[p])‖ = 1 := by
      have : ((2 : ℤ_[p]) * (t : ℤ_[p])) = ((2 * t : ℤ) : ℤ_[p]) := by push_cast; ring
      rw [this]

      have hn : ¬ (p : ℤ) ∣ 2 * t := by
        intro h
        rcases (Int.Prime.dvd_mul' hp.out h) with h | h
        · have : (p : ℤ) ∣ 2 := h
          have hp2' : p ∣ 2 := by exact_mod_cast this
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hp2')
        · exact hpt h
      have hle := PadicInt.norm_le_one ((2 * t : ℤ) : ℤ_[p])
      have hlt : ¬ ‖((2 * t : ℤ) : ℤ_[p])‖ < 1 := by rw [PadicInt.norm_int_lt_one_iff_dvd]; exact hn
      exact le_antisymm hle (not_lt.mp hlt)
    rw [h2, one_pow]
    exact h1
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  rw [hF] at hz
  exact sub_eq_zero.mp hz

theorem eq_primesEquiv_symm (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    v = (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩ := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  show Rat.HeightOneSpectrum.natGenerator v = p
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ p := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hv
    rw [map_natCast] at this
    exact_mod_cast this
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).mp hdvd

theorem main (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) (hsq : IsSquare (u : ZMod p)) :
    ∃ s : v.adicCompletion ℚ, s ^ 2 = algebraMap ℚ (v.adicCompletion ℚ) (u : ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_sq_eq_padicInt p hp2 u hu hsq
  have hv' := eq_primesEquiv_symm p hp v hv
  subst hv'
  let e := Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, hp⟩
  refine ⟨e (z : ℚ_[p]), ?_⟩
  rw [← map_pow]
  have hz' : ((z : ℚ_[p])) ^ 2 = algebraMap ℚ ℚ_[p] (u : ℚ) := by
    rw [← PadicInt.coe_pow, hz]
    simp
  rw [hz']
  exact e.toAlgEquiv.commutes (u : ℚ)

end HenselOddChi

theorem solution
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : (p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) (hsq : IsSquare (u : ZMod p)) :
    ∃ s : v.adicCompletion ℚ, s ^ 2 = algebraMap ℚ (v.adicCompletion ℚ) (u : ℚ) :=
  HenselOddChi.main p hp hp2 v hv u hu hsq

end S_Rat_exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd
end P2MW
export P2MW.S_Rat_exists_sq_eq_adicCompletion_of_isSquare_zmod_of_odd (solution)
