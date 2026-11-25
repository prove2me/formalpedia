-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.KerSplit.splitsAt_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:01.30418+00:00
-- url     : https://prove2.me/submissions/76c5c7cc-f564-4e14-822d-cf4ff5be6711

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KernelSplitting_IsIntegralHalf
import Theorems.Thm_PI_UnitaryGroupMassFormula_KerSplit_isIntegral_sqrt
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
    (cj : E ≃ₐ[ℚ] E) (d p : ℕ) (s : K) (hs : s * s = -(d : K))
    (hcj : cj (algebraMap K E s) = -algebraMap K E s) (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : jacobiSym (-(d : ℤ)) p = 1) : PI.KerIso.SplitsAt K cj p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, hpP⟩ := exists_isPrime_natCast_mem (K := K) p hp
  obtain ⟨r, t, ht⟩ : ∃ r t : ℤ, r * r + (d : ℤ) = (p : ℤ) * t := by
    obtain ⟨c, hc⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
    obtain ⟨t, ht⟩ : (p : ℤ) ∣ (c.val : ℤ) * (c.val : ℤ) + d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      push_cast at hc
      linear_combination -hc
    exact ⟨_, t, ht⟩
  have hg : Int.gcd (-(d : ℤ)) (p : ℤ) = 1 := by
    by_contra h
    have h0 := (jacobiSym.eq_zero_iff_not_coprime (a := -(d : ℤ)) (b := p)).2 h
    rw [hJ] at h0
    exact one_ne_zero h0
  obtain ⟨x, y, hxy⟩ := Int.isCoprime_iff_gcd_eq_one.2 hg
  obtain ⟨sO, hsK⟩ : ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = s := ⟨⟨s, isIntegral_sqrt d s hs⟩, rfl⟩
  have hinj := IsFractionRing.injective (𝓞 K) K
  have hss : sO * sO = -((d : ℕ) : 𝓞 K) :=
    hinj (by rw [map_mul, hsK, map_neg, map_natCast]; exact hs)
  have hprod : ((r : 𝓞 K) + sO) * ((r : 𝓞 K) - sO) = ((p : ℕ) : 𝓞 K) * (t : 𝓞 K) := by
    have h1 : ((r * r + d : ℤ) : 𝓞 K) = ((p * t : ℤ) : 𝓞 K) := by rw [ht]
    push_cast at h1
    linear_combination h1 - hss
  have hab : ((r : 𝓞 K) + sO) * ((r : 𝓞 K) - sO) ∈ P := by
    rw [hprod]
    exact P.mul_mem_right _ hpP
  have hnot : ¬ ((r : 𝓞 K) + sO ∈ P ∧ (r : 𝓞 K) - sO ∈ P) := by
    rintro ⟨h1, h2⟩
    have h2s : (2 : 𝓞 K) * sO ∈ P := by
      have h3 := P.sub_mem h1 h2
      rwa [show (r : 𝓞 K) + sO - ((r : 𝓞 K) - sO) = 2 * sO by ring] at h3
    obtain ⟨q, hq⟩ := hp.odd_of_ne_two hp2
    have hc' : (((q + 1 : ℕ)) : 𝓞 K) * 2 = ((p : ℕ) : 𝓞 K) + 1 := by
      rw [hq]
      push_cast
      ring
    have hsP : sO ∈ P := by
      have e : sO = (((q + 1 : ℕ)) : 𝓞 K) * (2 * sO) - sO * ((p : ℕ) : 𝓞 K) := by
        linear_combination (-sO) * hc'
      rw [e]
      exact P.sub_mem (P.mul_mem_left _ h2s) (P.mul_mem_left _ hpP)
    have hdP : ((d : ℕ) : 𝓞 K) ∈ P := by
      have h4 := P.mul_mem_left sO hsP
      rw [hss] at h4
      exact (P.neg_mem_iff).1 h4
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : 𝓞 K) = ((x : ℤ) : 𝓞 K) * (-((d : ℕ) : 𝓞 K)) + (y : 𝓞 K) * ((p : ℕ) : 𝓞 K) := by
      have h5 := congrArg (fun z : ℤ => (z : 𝓞 K)) hxy
      push_cast at h5
      exact h5.symm
    rw [e1]
    exact P.add_mem (P.mul_mem_left _ (P.neg_mem hdP)) (P.mul_mem_left _ hpP)
  have hca : cj (algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) + sO))) =
      algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) - sO)) := by
    simp only [map_add, map_sub, map_neg, map_intCast, hsK, hcj, sub_eq_add_neg]
  have hcb : cj (algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) - sO))) =
      algebraMap K E (algebraMap (𝓞 K) K ((r : 𝓞 K) + sO)) := by
    simp only [map_add, map_sub, map_neg, map_intCast, hsK, hcj, sub_eq_add_neg, neg_neg]
  have hcoe : ∀ z : 𝓞 K, (z : K) = algebraMap (𝓞 K) K z := fun _ => rfl
  rcases hP.mem_or_mem hab with ha | hb
  · refine ⟨P, hP, hpP, (r : 𝓞 K) + sO, (r : 𝓞 K) - sO, ?_, ha, fun hb => hnot ⟨ha, hb⟩⟩
    rw [hcoe, hcoe]
    exact hca
  · refine ⟨P, hP, hpP, (r : 𝓞 K) - sO, (r : 𝓞 K) + sO, ?_, hb, fun ha => hnot ⟨ha, hb⟩⟩
    rw [hcoe, hcoe]
    exact hcb
end PI.UnitaryGroupMassFormula.KerSplit
