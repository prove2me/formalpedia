-- Prove2me | solution 1 for QH.exists_coprime_primePairSetSecond_eq_PPset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:19.750621+00:00
-- url     : https://prove2.me/submissions/62abe85f-5031-4fe3-bae1-6a88d9d4365e

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_ExistsCoprimePrimePairSetSecondEqPPset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace QH
private theorem oddM_odd (z : ℝ) (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) : Nat.Coprime 2 (oddM z q) := by
  have hq2 : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm h2)
  refine Nat.Coprime.mul_right hq2 (Nat.Coprime.prod_right fun p hp => ?_)
  have hp' := Finset.mem_filter.mp hp
  have h3 : 3 ≤ p := (Finset.mem_Icc.mp hp'.1).1
  exact (Nat.coprime_primes Nat.prime_two hp'.2).mpr (by omega)
private theorem chineseRemainder_finiteCover (M : ℕ) (h : Nat.Coprime 2 M) : ∃ a : ℕ, a.Coprime (16 * M) ∧
    ∀ d : ℕ, (d % 16 = 7 ∧ M ∣ d + 1) ↔ d % (16 * M) = a % (16 * M) := by
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at h
  have h16 : Nat.Coprime 16 M := by
    have := Nat.Coprime.pow_left 4 h
    norm_num at this
    exact this
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder h16 7 (M - 1)
  have hc3 : c + 1 ≡ 0 [MOD M] := by
    have := hc2.add_right 1
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hM0)] at this
    exact this.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
  have hc1' : c % 16 = 7 := hc1
  have key1 : ∀ d : ℕ, d % 16 = 7 ↔ d ≡ c [MOD 16] := by
    intro d
    unfold Nat.ModEq
    rw [hc1']
  have key2 : ∀ d : ℕ, M ∣ d + 1 ↔ d ≡ c [MOD M] := by
    intro d
    rw [← Nat.modEq_zero_iff_dvd]
    constructor
    · intro hd
      exact Nat.ModEq.add_right_cancel' 1 (hd.trans hc3.symm)
    · intro hd
      exact (hd.add_right 1).trans hc3
  have hcM : Nat.Coprime c M := by
    have hdvd : M ∣ c + 1 := Nat.modEq_zero_iff_dvd.mp hc3
    have hcc : Nat.Coprime c (c + 1) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.coprime_one_right c
    exact Nat.Coprime.coprime_dvd_right hdvd hcc
  have hc16 : Nat.Coprime c 16 := by
    have := Nat.ModEq.gcd_eq hc1
    unfold Nat.Coprime
    rw [this]
    norm_num
  refine ⟨c, Nat.Coprime.mul_right hc16 hcM, fun d => ?_⟩
  rw [key1 d, key2 d]
  exact Nat.modEq_and_modEq_iff_modEq_mul h16
end QH
end

set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∀ (z z' : ℝ) (q : ℕ), q.Prime → q ≠ 2 → ∃ a₀ : ℕ, a₀.Coprime (16 * oddM z q) ∧
      primeSetTwoBounds z z' q = PPset (16 * oddM z q) a₀ (Real.exp z') := by
  intro z z' q hq h2
  obtain ⟨a, ha, hiff⟩ := chineseRemainder_finiteCover _ (oddM_odd z q hq h2)
  refine ⟨a, ha, ?_⟩
  unfold primeSetTwoBounds PPset
  apply Finset.filter_congr
  intro d _
  rw [← hiff d]
  tauto
end QH
