-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.ana_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:43.845411+00:00
-- url     : https://prove2.me/submissions/d0ecd17a-b050-4fc7-ad32-7ea48b583041

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_AnaCore
import Theorems.Thm_PI_SqfPrimeFactor_W_ana_log_le
import Theorems.Thm_PI_SqfPrimeFactor_W_ana_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open Finset
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (hRS : PI.PrimesDyadicRS.Claim) (g r : ℕ) (hr : 100 ≤ r) (hg : 2 ^ 12 ≤ g)
    (S : Finset ℕ) (hS : ∀ p, p ∈ S ↔ p.Prime ∧ r < 2 * p ∧ p + 3 ≤ r) :
    (g : ℝ) ^ r - ∑ p ∈ S, ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) ≤
      (1 - 1 / (5 * Real.log r)) * (g : ℝ) ^ r := by
  have hrR : (100 : ℝ) ≤ r := by exact_mod_cast hr
  have hR := hRS ((r : ℝ) / 2) (by linarith)
  have hf1 : ⌊2 * ((r : ℝ) / 2)⌋₊ = r := by
    rw [mul_div_cancel₀ _ two_ne_zero]; exact Nat.floor_natCast r
  have hf2 : ⌊(r : ℝ) / 2⌋₊ = r / 2 := by
    rw [Nat.floor_div_ofNat, Nat.floor_natCast]
  rw [hf1, hf2] at hR
  have hcnt : (Nat.primeCounting r : ℝ) ≤ Nat.primeCounting (r / 2) + S.card + 2 := by
    exact_mod_cast ana_pi r hr S hS
  set L := Real.log r with hL
  have hL2 : Real.log ((r : ℝ) / 2) < L := Real.log_lt_log (by linarith) (by linarith)
  have hL2p : 0 < Real.log ((r : ℝ) / 2) := Real.log_pos (by linarith)
  have hLp : 0 < L := by linarith
  have hLle : L ≤ 0.0464 * r := ana_log_le r hrR

  have h3 : 3 * ((r : ℝ) / 2) / (5 * L) ≤ 3 * ((r : ℝ) / 2) / (5 * Real.log ((r : ℝ) / 2)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hc0 : 3 * ((r : ℝ) / 2) / (5 * L) < S.card + 2 := by linarith
  rw [div_lt_iff₀ (by positivity)] at hc0
  have hcl : (r : ℝ) ≤ S.card * (5 * L) * (4095 / 4096) := by nlinarith

  have hg0 : (4096 : ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < g := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hterm : ∀ p ∈ S, (g : ℝ) ^ r * (4095 / 4096) / r ≤
      ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) := by
    intro p hp
    obtain ⟨hpp, h2, h3⟩ := (hS p).1 hp
    have hp2 : 2 ≤ p := hpp.two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hpr : (p : ℝ) ≤ r := by exact_mod_cast (show p ≤ r by omega)
    have hsplit : (g : ℝ) ^ r = (g : ℝ) ^ p * (g : ℝ) ^ (r - p) := by
      rw [← pow_add]; congr 1; omega
    have hgp2 : (g : ℝ) ^ 2 ≤ (g : ℝ) ^ p := pow_le_pow_right₀ (by linarith) hp2
    have hgp : (g : ℝ) * 4096 ≤ (g : ℝ) ^ p := by nlinarith
    have hq : (0 : ℝ) ≤ (g : ℝ) ^ (r - p) := by positivity
    have hgpp : (0 : ℝ) < (g : ℝ) ^ p := by positivity
    rw [hsplit]
    calc (g : ℝ) ^ p * (g : ℝ) ^ (r - p) * (4095 / 4096) / r
        ≤ (g : ℝ) ^ p * (g : ℝ) ^ (r - p) * (4095 / 4096) / p :=
          div_le_div_of_nonneg_left (by positivity) hp0 hpr
      _ = ((g : ℝ) ^ p * (4095 / 4096)) / p * (g : ℝ) ^ (r - p) := by ring
      _ ≤ ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) := by
          apply mul_le_mul_of_nonneg_right _ hq
          apply div_le_div_of_nonneg_right _ hp0.le
          linarith
  have hsum : S.card * ((g : ℝ) ^ r * (4095 / 4096) / r) ≤
      ∑ p ∈ S, ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) := by
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hG : (0 : ℝ) < (g : ℝ) ^ r := by positivity
  have hkey : (g : ℝ) ^ r / (5 * L) ≤ S.card * ((g : ℝ) ^ r * (4095 / 4096) / r) := by
    rw [div_le_iff₀ (by positivity)]
    have : S.card * ((g : ℝ) ^ r * (4095 / 4096) / r) * (5 * L) =
        (g : ℝ) ^ r * (S.card * (5 * L) * (4095 / 4096)) / r := by ring
    rw [this, le_div_iff₀ hrpos]
    exact mul_le_mul_of_nonneg_left hcl hG.le
  have : (1 - 1 / (5 * L)) * (g : ℝ) ^ r = (g : ℝ) ^ r - (g : ℝ) ^ r / (5 * L) := by ring
  rw [this]
  linarith
end PI.SqfPrimeFactor.W
