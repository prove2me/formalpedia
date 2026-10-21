-- Prove2me | solution 1 for SensitivityCampaign.reach_21303_gamma
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-20T06:18:41.395408+00:00
-- url     : https://prove2.me/submissions/27e9bcac-bca9-497a-b928-de427b981c65

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_coupled_gamma_periodic_seeds
import Theorems.Thm_SensitivityCampaign_finite_certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 4096

/-! Integer certificates for arbitrary periodic amplification gains.  Nothing in
this file depends on a particular number of stages, a tournament size, or a
decimal target.  In particular, `g` may be the product of unequal stage gains.
-/

namespace SensitivityPeriodicArithmetic

theorem absorb_overhead (c h p : ℕ) (hc : c ≤ 2 ^ h) :
    c ^ p ≤ 2 ^ (h * p) := by
  simpa only [← pow_mul] using Nat.pow_le_pow_left hc p

theorem seed_power (c r g p q m : ℕ)
    (hg : 2 * r ^ p ≤ g ^ q) (ho : c ^ p ≤ 2 ^ m) :
    (c * r ^ m) ^ p ≤ (g ^ m) ^ q := by
  calc
    (c * r ^ m) ^ p = c ^ p * (r ^ p) ^ m := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul, ← pow_mul, Nat.mul_comm m p]
    _ ≤ 2 ^ m * (r ^ p) ^ m := Nat.mul_le_mul_right _ ho
    _ = (2 * r ^ p) ^ m := (mul_pow _ _ _).symm
    _ ≤ (g ^ q) ^ m := Nat.pow_le_pow_left hg _
    _ = (g ^ m) ^ q := by rw [← pow_mul, ← pow_mul, Nat.mul_comm q m]

/-- The equality `ha` permits an exact decimal target without changing it to a
fraction in the statement. All certification remains integer arithmetic. -/
theorem real_power {a b p q : ℕ} {α : ℝ}
    (hq : q ≠ 0) (ha : α * (q : ℝ) = (p : ℝ))
    (h : a ^ p ≤ b ^ q) : (a : ℝ) ^ α ≤ (b : ℝ) := by
  have hr : (a : ℝ) ^ p ≤ (b : ℝ) ^ q := by exact_mod_cast h
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Nat.cast_nonneg _) hq).mp
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _), ha, Real.rpow_natCast]
  exact hr

theorem periodic_real_power (c r g h p q : ℕ) (α : ℝ)
    (hc : c ≤ 2 ^ h) (hg : 2 * r ^ p ≤ g ^ q)
    (hq : q ≠ 0) (ha : α * (q : ℝ) = (p : ℝ)) :
    ((c * r ^ (h * p) : ℕ) : ℝ) ^ α ≤ ((g ^ (h * p) : ℕ) : ℝ) :=
  real_power hq ha (seed_power c r g p q (h * p) hg (absorb_overhead c h p hc))

end SensitivityPeriodicArithmetic

namespace SensitivityPeriodicArithmetic

open OAI.Paper320

/-- A generic finite-certificate interface for a periodic construction. Here
`g` is the product of all stage block gains in one period. The period may use
different tournament sizes. The target `α` is preserved literally. -/
theorem achieves_of_periodic_input (c r g h p q : ℕ) (α : ℝ)
    (hc : 1 < c) (hr : 0 < r) (hg : 1 < g)
    (hh : 0 < h) (hp : 0 < p) (hq : q ≠ 0) (hα : 0 ≤ α)
    (hcover : c ≤ 2 ^ h) (hgap : 2 * r ^ p ≤ g ^ q)
    (hexact : α * (q : ℝ) = (p : ℝ))
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool)
      (x : Fin n → Bool),
      sensitivity f ≤ c * r ^ m ∧ g ^ m ≤ blockSensitivityAt f x) :
    SensitivityCampaign.AchievesExponent α := by
  obtain ⟨n, f, x, hs, hb⟩ := hseed (h * p)
  have hA : 1 < c * r ^ (h * p) :=
    hc.trans_le (Nat.le_mul_of_pos_right c (pow_pos hr _))
  have hB : 1 < g ^ (h * p) := one_lt_pow₀ hg (Nat.ne_of_gt (Nat.mul_pos hh hp))
  exact SensitivityCampaign.finite_certificate f x
    (c * r ^ (h * p)) (g ^ (h * p)) α hA hB hα hs hb
    (periodic_real_power c r g h p q α hcover hgap hq hexact)

/-- A convenient zero-input version, matching the actual tournament assembly. -/
theorem achieves_of_periodic_zero (c r g h p q : ℕ) (α : ℝ)
    (hc : 1 < c) (hr : 0 < r) (hg : 1 < g)
    (hh : 0 < h) (hp : 0 < p) (hq : q ≠ 0) (hα : 0 ≤ α)
    (hcover : c ≤ 2 ^ h) (hgap : 2 * r ^ p ≤ g ^ q)
    (hexact : α * (q : ℝ) = (p : ℝ))
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      sensitivity f ≤ c * r ^ m ∧ g ^ m ≤ blockSensitivityAt f (fun _ => false)) :
    SensitivityCampaign.AchievesExponent α := by
  apply achieves_of_periodic_input c r g h p q α hc hr hg hh hp hq hα
    hcover hgap hexact
  intro m
  obtain ⟨n, f, hs, hb⟩ := hseed m
  exact ⟨n, f, fun _ => false, hs, hb⟩

end SensitivityPeriodicArithmetic

theorem solution : SensitivityCampaign.AchievesExponent (2.1303 : ℝ) := by
  apply SensitivityPeriodicArithmetic.achieves_of_periodic_zero
    3418946681687790375032 50063687 25260794820729601 72 21303 10000 (2.1303 : ℝ)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · norm_num
  · decide
  · decide
  · norm_num
  · exact SensitivityCampaign.coupled_gamma_periodic_seeds
#print axioms solution
