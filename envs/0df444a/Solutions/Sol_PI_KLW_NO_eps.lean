-- Prove2me | solution 1 for PI.KLW.NO.eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:23.976214+00:00
-- url     : https://prove2.me/submissions/286578dd-4631-47ae-81e2-26077ffbc6d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Theorems.Thm_PI_KLW_NO_natCast_mem_O
import Theorems.Thm_PI_KLW_NO_intCast_mem_O
import Theorems.Thm_PI_KLW_NO_rp_mul
import Theorems.Thm_PI_KLW_NO_fixed_int
import Theorems.Thm_PI_KLW_NO_rp_div_int
import Theorems.Thm_PI_KLW_NO_ne_of_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO
namespace PI.KLW.NO
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hK : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (hs : SplitK c p) (k : ℕ) :
    ∃ ε : K, Rp K p ε ∧ ε + c ε = 1 ∧ Rp K p (ε * c ε / (p : K) ^ k) := by
  have hne := ne_of_split c hs
  obtain ⟨P, hP, hpP, a, b, hab, ha, hb⟩ := hs
  have hBA : c (b : K) = (a : K) := by rw [← hab, hc]
  have hfix : c ((a : K) ^ (k + 1) + (b : K) ^ (k + 1)) = (a : K) ^ (k + 1) + (b : K) ^ (k + 1) := by
    rw [map_add, map_pow, map_pow, hab, hBA, add_comm]
  have hO : (a : K) ^ (k + 1) + (b : K) ^ (k + 1) ∈ (algebraMap (𝓞 K) K).range :=
    ⟨a ^ (k + 1) + b ^ (k + 1), by rw [map_add, map_pow, map_pow]⟩
  obtain ⟨m, hm⟩ := fixed_int c hK hne hfix hO
  have hdvd : ¬ (p : ℤ) ∣ m := by
    rintro ⟨m', hm'⟩
    apply hb
    have e : a ^ (k + 1) + b ^ (k + 1) = (p : 𝓞 K) * (m' : 𝓞 K) := by
      apply RingOfIntegers.coe_injective
      rw [map_add, map_pow, map_pow, map_mul, map_natCast, map_intCast]
      have : (m : K) = (p : K) * m' := by rw [hm']; push_cast; ring
      exact hm.trans this
    have h1 : a ^ (k + 1) + b ^ (k + 1) ∈ P := by rw [e]; exact P.mul_mem_right _ hpP
    have h2 : b ^ (k + 1) ∈ P :=
      (P.add_mem_iff_right (P.pow_mem_of_mem ha (k + 1) (Nat.succ_pos k))).1 h1
    exact hP.mem_of_pow_mem _ h2
  have hm0 : m ≠ 0 := by rintro rfl; exact hdvd (dvd_zero _)
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm0

  have hfixN : c ((a : K) * b) = (a : K) * b := by rw [map_mul, hab, hBA, mul_comm]
  have hON : (a : K) * b ∈ (algebraMap (𝓞 K) K).range := ⟨a * b, by rw [map_mul]⟩
  obtain ⟨n, hn⟩ := fixed_int c hK hne hfixN hON
  have hpn : (p : ℤ) ∣ n := by
    by_contra hnd
    have hcop : IsCoprime (p : ℤ) n := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime p n.natAbs :=
        (Nat.Prime.coprime_iff_not_dvd hp).2 (by rwa [← Int.natCast_dvd])
      exact this
    obtain ⟨u, v, huv⟩ := hcop
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 K) = (u : 𝓞 K) * (p : 𝓞 K) + (v : 𝓞 K) * (a * b) := by
      apply RingOfIntegers.coe_injective
      rw [map_one, map_add, map_mul, map_mul, map_mul, map_intCast, map_intCast, map_natCast]
      have : ((u * p + v * n : ℤ) : K) = 1 := by rw [huv]; simp
      rw [← this]; push_cast
      have hn' : algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K b = (n : K) := hn
      rw [hn']
    rw [e]
    exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ (P.mul_mem_right _ ha))
  obtain ⟨n₁, hn₁⟩ := hpn
  have hab' : (a : K) * b = (p : K) * n₁ := by rw [hn, hn₁]; push_cast; ring
  refine ⟨(b : K) ^ (k + 1) / m, rp_div_int ⟨b ^ (k + 1), by rw [map_pow]⟩ hdvd hp, ?_, ?_⟩
  · rw [map_div₀, map_pow, hBA, map_intCast, ← add_div, add_comm, hm, div_self hmK]
  · rw [map_div₀, map_pow, hBA, map_intCast]
    have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
    have e1 : (b : K) ^ (k + 1) * (a : K) ^ (k + 1) = (p : K) ^ k * ((p : K) * (n₁ : K) ^ (k + 1)) := by
      rw [← mul_pow, mul_comm (b : K), hab', mul_pow, pow_succ]; ring
    have e2 : (b : K) ^ (k + 1) / m * ((a : K) ^ (k + 1) / m) / (p : K) ^ k
        = ((p : K) * (n₁ : K) ^ (k + 1) / m) * (1 / m) := by
      rw [show (b : K) ^ (k + 1) / m * ((a : K) ^ (k + 1) / m) / (p : K) ^ k
          = ((b : K) ^ (k + 1) * (a : K) ^ (k + 1)) / (p : K) ^ k / (m * m) by ring, e1,
        mul_div_cancel_left₀ _ (pow_ne_zero _ hp0)]
      ring
    rw [e2]
    exact rp_mul (rp_div_int (Subring.mul_mem _ (natCast_mem_O p) (Subring.pow_mem _ (intCast_mem_O n₁) _)) hdvd hp)
      (rp_div_int (Subring.one_mem _) hdvd hp)
end PI.KLW.NO
