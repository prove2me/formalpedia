-- Prove2me | solution 1 for Rat.exists_ternary_isotropic_adicCompletion_of_intCast_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5a0df304-b9d9-5234-b639-fa25ed6d1701

import Mathlib
import Theorems.Thm_Padic_exists_ternary_isotropic_of_norm_eq_one_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LocUnit

theorem natGenerator_dvd_natAbs_iff (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℤ) :
    (Rat.HeightOneSpectrum.natGenerator v ∣ k.natAbs) ↔ ((k : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
  have h1 : ((k.natAbs : ℕ) : ℤ) ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) ↔
      (k : ℤ) ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    rcases Int.natAbs_eq k with h | h
    · rw [← h]
    · conv_rhs => rw [h]
      rw [Ideal.neg_mem_iff]
  rw [h1]
  have h2 : (k : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((k : ℤ) : 𝓞 ℚ) := by
    rw [map_intCast, Int.cast_id]
  conv_lhs => rw [h2]
  rw [Ideal.apply_mem_of_equiv_iff]

end LocUnit

open LocUnit in
theorem solution
    (m n : ℤ) (v : HeightOneSpectrum (𝓞 ℚ))
    (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) (hm : ((m : ℤ) : 𝓞 ℚ) ∉ v.asIdeal) (hn : ((n : ℤ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) (m : ℚ)) * x ^ 2
        - (algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ)) * y ^ 2 = 0 := by
  classical
  set p : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v with hp
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  have hgen : (Rat.HeightOneSpectrum.natGenerator v : ℕ) = (p : ℕ) := rfl

  have hmem : ∀ k : ℤ, ((p : ℕ) : ℤ) ∣ k ↔ ((k : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro k
    rw [Int.natCast_dvd, ← hgen]
    exact natGenerator_dvd_natAbs_iff v k

  have hp2 : (p : ℕ) ≠ 2 := by
    intro h
    apply h2
    have : ((2 : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := (hmem 2).mp (by rw [h]; norm_num)
    simpa using this

  have hnorm : ∀ k : ℤ, ((k : ℤ) : 𝓞 ℚ) ∉ v.asIdeal → ‖((k : ℤ) : ℚ_[p])‖ = 1 := by
    intro k hk
    have hndvd : ¬ ((p : ℕ) : ℤ) ∣ k := fun hd => hk ((hmem k).mp hd)
    refine le_antisymm (Padic.norm_int_le_one k) ?_
    exact not_lt.mp (mt Padic.norm_intCast_lt_one_iff.mp hndvd)

  obtain ⟨z, x, y, hne, heq⟩ :=
    Padic.exists_ternary_isotropic_of_norm_eq_one_of_ne_two (p : ℕ) hp2 ((m : ℤ) : ℚ_[p]) ((n : ℤ) : ℚ_[p])
      (hnorm m hm) (hnorm n hn)

  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have hcomm : ∀ k : ℤ, e.symm ((k : ℤ) : ℚ_[p]) = algebraMap ℚ (v.adicCompletion ℚ) (k : ℚ) := by
    intro k
    have : ((k : ℤ) : ℚ_[p]) = algebraMap ℚ ℚ_[p] ((k : ℤ) : ℚ) := by simp
    rw [this]
    exact AlgHomClass.commutes e.symm ((k : ℤ) : ℚ)
  refine ⟨e.symm z, e.symm x, e.symm y, ?_, ?_⟩
  · rintro ⟨hz, hx, hy⟩
    apply hne
    refine ⟨?_, ?_, ?_⟩
    · simpa using congrArg e hz
    · simpa using congrArg e hx
    · simpa using congrArg e hy
  · have h := congrArg e.symm heq
    rw [map_zero] at h
    rw [← h]
    simp only [map_sub, map_mul, map_pow, hcomm]

end S_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem
end P2MW
export P2MW.S_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem (solution)
