-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.KerSplit.splitsAt_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:03.190589+00:00
-- url     : https://prove2.me/submissions/7adb8205-d336-4abf-ad98-3994e50a1123

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KernelSplitting_IsIntegralHalf
import Theorems.Thm_PI_UnitaryGroupMassFormula_KerSplit_isIntegral_half
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField Polynomial
namespace PI.UnitaryGroupMassFormula.KerSplit
private theorem exists_isPrime_natCast_mem {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ ((p : ℕ) : 𝓞 K) ∈ P := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 K) := by
    rintro ⟨v, hv⟩
    have h1 : algebraMap (𝓞 K) K (↑v⁻¹ : 𝓞 K) * (p : K) = 1 := by
      rw [← map_natCast (algebraMap (𝓞 K) K) p, ← map_mul, ← hv, Units.inv_mul, map_one]
    have h2 : algebraMap (𝓞 K) K (↑v⁻¹ : 𝓞 K) = algebraMap ℚ K ((p : ℚ)⁻¹) := by
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_left h1
    have hint : IsIntegral ℤ (algebraMap ℚ K ((p : ℚ)⁻¹)) := by
      rw [← h2]
      exact RingOfIntegers.isIntegral_coe _
    have hq : IsIntegral ℤ ((p : ℚ)⁻¹) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ K) (algebraMap ℚ K).injective).1 hint
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hn' : (n : ℚ) = (p : ℚ)⁻¹ := by simpa using hn
    have h4 : ((n * p : ℤ) : ℚ) = 1 := by
      push_cast
      rw [hn']
      exact inv_mul_cancel₀ hp0
    have h5 : n * (p : ℤ) = 1 := by exact_mod_cast h4
    have h6 : (p : ℤ) ∣ 1 := ⟨n, by rw [mul_comm]; exact h5.symm⟩
    have h7 := Int.eq_one_of_dvd_one (by positivity) h6
    have h8 : p = 1 := by exact_mod_cast h7
    exact hp.one_lt.ne' h8
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  exact ⟨M, hM.isPrime, hle (Ideal.subset_span (Set.mem_singleton _))⟩
end PI.UnitaryGroupMassFormula.KerSplit
end
end

set_option autoImplicit false
noncomputable section
open NumberField Polynomial
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.KerSplit
namespace PI.UnitaryGroupMassFormula.KerSplit
theorem _root_.solution {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (cj : E ≃ₐ[ℚ] E) (d : ℕ) (s : K) (hd : d % 8 = 7) (hs : s * s = -(d : K))
    (hcj : cj (algebraMap K E s) = -algebraMap K E s) : PI.KerIso.SplitsAt K cj 2 := by
  obtain ⟨P, hP, h2P⟩ := exists_isPrime_natCast_mem (K := K) 2 Nat.prime_two
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 8 * m := ⟨(d + 1) / 8, by omega⟩
  have hmK : (d : K) + 1 = 8 * (m : K) := by exact_mod_cast hm
  obtain ⟨aO, haK⟩ : ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = (1 + s) / 2 :=
    ⟨⟨_, isIntegral_half d s hd hs⟩, rfl⟩
  obtain ⟨bO, hbK⟩ : ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = (1 + -s) / 2 :=
    ⟨⟨_, isIntegral_half d (-s) hd (by rw [neg_mul_neg]; exact hs)⟩, rfl⟩
  have hinj := IsFractionRing.injective (𝓞 K) K
  have hsum : aO + bO = 1 := hinj (by rw [map_add, haK, hbK, map_one]; ring)
  have hprod : aO * bO = ((2 : ℕ) : 𝓞 K) * (m : 𝓞 K) := hinj (by
    rw [map_mul, haK, hbK, map_mul, map_natCast, map_natCast]
    push_cast
    linear_combination (-1 / 4 : K) * hs + (1 / 4 : K) * hmK)
  have hca : cj (algebraMap K E ((1 + s) / 2)) = algebraMap K E ((1 + -s) / 2) := by
    simp only [map_div₀, map_add, map_neg, map_one, map_ofNat, hcj]
  have hcb : cj (algebraMap K E ((1 + -s) / 2)) = algebraMap K E ((1 + s) / 2) := by
    simp only [map_div₀, map_add, map_neg, map_one, map_ofNat, hcj, neg_neg]
  have hab : aO * bO ∈ P := by
    rw [hprod]
    exact P.mul_mem_right _ h2P
  have hcoe : ∀ x : 𝓞 K, (x : K) = algebraMap (𝓞 K) K x := fun _ => rfl
  rcases hP.mem_or_mem hab with ha | hb
  · refine ⟨P, hP, h2P, aO, bO, ?_, ha, fun hb => hP.ne_top ?_⟩
    · rw [hcoe, hcoe, haK, hbK]
      exact hca
    · rw [Ideal.eq_top_iff_one, ← hsum]
      exact P.add_mem ha hb
  · refine ⟨P, hP, h2P, bO, aO, ?_, hb, fun ha => hP.ne_top ?_⟩
    · rw [hcoe, hcoe, haK, hbK]
      exact hcb
    · rw [Ideal.eq_top_iff_one, ← hsum]
      exact P.add_mem ha hb
end PI.UnitaryGroupMassFormula.KerSplit
