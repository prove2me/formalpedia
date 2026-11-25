-- Prove2me | solution 1 for UpperTheory.T3.exists_three_primes_one_mod_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:51:21.68836+00:00
-- url     : https://prove2.me/submissions/cfbfc587-f13c-4c4b-8b9e-c5c5fab063ba

import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ShortNorm
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ExistsThreePrimesOneModLeRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.Mem.An
namespace UpperTheory.T3
private theorem mod_eq_one_of_mod_mul {p M K : ℕ} (h : p % (M * K) = 1) (hM : 1 < M) : p % M = 1 := by
  rw [← Nat.mod_mul_right_mod p M K, h, Nat.mod_eq_of_lt hM]
end UpperTheory.T3
end

set_option autoImplicit false
open GlobalTheory.Mem.An
open UpperTheory UpperTheory.T3
namespace UpperTheory.T3
theorem _root_.solution :
    SmallOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N → ∃ p p' q0 : ℕ, p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧
      p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 := by
  intro hS
  obtain ⟨A, hA1, hA⟩ := hS
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hAA : A ≤ A * A := by nlinarith
  have hAAA : 0 ≤ A * A * A := by positivity
  refine ⟨(1 + (2 * A + (2 * A + 2) * A)) * A, by nlinarith, ?_⟩
  intro N hN
  have hx : (30 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hx1 : (1 : ℝ) ≤ N := by linarith
  have key : ∀ (M : ℕ) (e : ℝ), 2 ≤ M → (M : ℝ) ≤ (N : ℝ) ^ e →
      ∃ q : ℕ, q.Prime ∧ q % M = 1 ∧ (q : ℝ) ≤ (N : ℝ) ^ (e * A) := by
    intro M e hM hle
    obtain ⟨q, hq, hqm, hqle⟩ := hA M hM
    refine ⟨q, hq, hqm, le_trans hqle ?_⟩
    rw [Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by linarith)
  obtain ⟨p, hp, hpm, hple⟩ := key (15 * N) 2 (by omega) (by
    push_cast
    rw [Real.rpow_two]
    nlinarith)
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨p', hp', hp'm, hp'le⟩ := key (p * (15 * N)) (2 * A + 2)
    (by
      have := Nat.mul_le_mul hp.two_le (show 1 ≤ 15 * N by omega)
      omega)
    (by
      push_cast
      rw [Real.rpow_add hx0, Real.rpow_two]
      exact mul_le_mul hple (by nlinarith) (by positivity) (by positivity))
  obtain ⟨q0, hq0, hq0m, hq0le⟩ := key (N * (p * p')) (1 + (2 * A + (2 * A + 2) * A))
    (by
      have := Nat.mul_le_mul (show 2 ≤ N by omega) (Nat.mul_pos hp.pos hp'.pos)
      omega)
    (by
      push_cast
      rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hple hp'le (Nat.cast_nonneg _) (by positivity)) hx0.le)
  have hp'p : p' % p = 1 := mod_eq_one_of_mod_mul hp'm hp1
  have hp'15 : p' % (15 * N) = 1 :=
    mod_eq_one_of_mod_mul (K := p) (by rw [Nat.mul_comm]; exact hp'm) (by omega)
  have hq0N : q0 % N = 1 := mod_eq_one_of_mod_mul hq0m (by omega)
  have hq0p : q0 % p = 1 :=
    mod_eq_one_of_mod_mul (K := p' * N) (by rw [show p * (p' * N) = N * (p * p') by ring]; exact hq0m) hp1
  have hq0p' : q0 % p' = 1 :=
    mod_eq_one_of_mod_mul (K := p * N) (by rw [show p' * (p * N) = N * (p * p') by ring]; exact hq0m) hp'.one_lt
  refine ⟨p, p', q0, hp, hp', hq0, ?_, ?_, ?_, hpm, hp'15, hq0N, ?_, ?_, hq0le⟩
  · intro h
    rw [← h, Nat.mod_self] at hp'p
    omega
  · intro h
    rw [h, Nat.mod_self] at hq0p
    omega
  · intro h
    rw [h, Nat.mod_self] at hq0p'
    omega
  · exact le_trans hple (Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith))
  · exact le_trans hp'le (Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith))
end UpperTheory.T3
