-- Prove2me | solution 1 for PI.TailWork.tail_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:48.053796+00:00
-- url     : https://prove2.me/submissions/46366be8-56ae-4f45-abf7-35546e1db79b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock
import Theorems.Thm_PI_TailWork_weighted
import Theorems.Thm_PI_TailWork_log_four_lt
import Theorems.Thm_PI_TailWork_weight_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset
namespace PI.TailWork
theorem _root_.solution (k : ℕ) (hk : 3 ≤ k) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / (2 * (k : ℝ) + 1) := by
  have hk1 : 1 ≤ k := by omega
  have hW := weighted k hk1 Q hQ
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hcpos : 0 < 3 - 1 / (2 * (k : ℝ) + 1) := by
    have : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hterm : ∀ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ Real.log (p : ℝ) * (g ((p + 1) / 2) - g p) / (3 - 1 / (2 * (k : ℝ) + 1)) := by
    intro p hp
    obtain ⟨hpr, hpk⟩ := hQ p hp
    have hodd : p % 2 = 1 := by
      rcases hpr.eq_two_or_odd with h2 | h2
      · omega
      · exact h2
    have hwg := weight_ge k p hk1 hpk hodd
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    rw [le_div_iff₀ hcpos]
    calc Real.log (p : ℝ) / (p : ℝ) ^ 2 * (3 - 1 / (2 * (k : ℝ) + 1))
        = Real.log (p : ℝ) * ((3 - 1 / (2 * (k : ℝ) + 1)) / (p : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwg hlog
  have hl := log_four_lt
  have hl0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have e : Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) / (3 - 1 / (2 * (k : ℝ) + 1))
      = Real.log 4 * (2 * (k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 1) * (6 * (k : ℝ) + 2)) := by
    have : (k : ℝ) ≠ 0 := by linarith
    have : (k : ℝ) + 1 ≠ 0 := by linarith
    have : 2 * (k : ℝ) + 1 ≠ 0 := by linarith
    have : 6 * (k : ℝ) + 2 ≠ 0 := by linarith
    have hc : 3 - 1 / (2 * (k : ℝ) + 1) = (6 * (k : ℝ) + 2) / (2 * (k : ℝ) + 1) := by
      field_simp
      ring
    rw [hc]
    field_simp
    ring
  have A : Real.log 4 * (2 * (k : ℝ) + 1) ^ 3 ≤ 1.3863 * (2 * (k : ℝ) + 1) ^ 3 :=
    mul_le_mul_of_nonneg_right hl.le (by positivity)
  have hk3 : 0 ≤ (k : ℝ) - 3 := by linarith
  have B : 1.3863 * (2 * (k : ℝ) + 1) ^ 3 ≤ 2.04 * ((k : ℝ) * ((k : ℝ) + 1) * (6 * (k : ℝ) + 2)) := by
    nlinarith [mul_nonneg (mul_nonneg hk3 hk3) hk3, mul_nonneg hk3 hk3, hk3]
  calc ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p) / (3 - 1 / (2 * (k : ℝ) + 1)) :=
        Finset.sum_le_sum hterm
    _ = (∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)) / (3 - 1 / (2 * (k : ℝ) + 1)) := by
        rw [Finset.sum_div]
    _ ≤ Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) / (3 - 1 / (2 * (k : ℝ) + 1)) :=
        div_le_div_of_nonneg_right hW hcpos.le
    _ ≤ 2.04 / (2 * (k : ℝ) + 1) := by
        rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [A, B]
end PI.TailWork
