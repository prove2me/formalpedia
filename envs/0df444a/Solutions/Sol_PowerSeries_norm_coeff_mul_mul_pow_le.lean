-- Prove2me | solution 1 for PowerSeries.norm_coeff_mul_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e9e41a62-6c6d-5029-99b8-f5d81038ce6c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_norm_coeff_mul_mul_pow_le

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace PowerSeries
p2m_export "PowerSeries" "coeff_mul coeff"
p2m_open "PowerSeries"

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

theorem l1_M_nonneg (F : PowerSeries L) {ρ M : ℝ}
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) : 0 ≤ M := by
  have := hF 0
  simp only [pow_zero, mul_one] at this
  exact (norm_nonneg _).trans this

end PowerSeries

open _root_.PowerSeries _root_.P2MW.S_PowerSeries_norm_coeff_mul_mul_pow_le.PowerSeries in

theorem solution {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 ≤ ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (n : ℕ) : ‖PowerSeries.coeff n (F * G)‖ * ρ ^ n ≤ M * M' := by
  have hM := l1_M_nonneg F hF
  have hM' := l1_M_nonneg G hG
  rw [PowerSeries.coeff_mul]
  rcases (pow_nonneg hρ n).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact mul_nonneg hM hM'
  have hC : 0 ≤ M * M' / ρ ^ n := div_nonneg (mul_nonneg hM hM') hpos.le
  have h : ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖
      ≤ M * M' / ρ ^ n := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [norm_mul, le_div_iff₀ hpos, ← hp, pow_add]
    calc ‖PowerSeries.coeff p.1 F‖ * ‖PowerSeries.coeff p.2 G‖ * (ρ ^ p.1 * ρ ^ p.2)
        = (‖PowerSeries.coeff p.1 F‖ * ρ ^ p.1) * (‖PowerSeries.coeff p.2 G‖ * ρ ^ p.2) := by ring
      _ ≤ M * M' := mul_le_mul (hF p.1) (hG p.2) (by positivity) hM
  exact (le_div_iff₀ hpos).mp h

#print axioms solution

end S_PowerSeries_norm_coeff_mul_mul_pow_le
end P2MW
export P2MW.S_PowerSeries_norm_coeff_mul_mul_pow_le (solution)
