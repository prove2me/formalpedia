-- Prove2me | solution 1 for PowerSeries.taylorShift_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/05c3a2aa-f8a8-5ba0-acee-41e3ef8cc970

import Mathlib
import Theorems.Thm_PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt
import Theorems.Thm_PowerSeries_norm_coeff_mul_mul_pow_le
import Theorems.Thm_PowerSeries_norm_coeff_taylorShift_mul_pow_le
import Theorems.Thm_PowerSeries_tsum_coeff_taylorShift_mul_pow_eq
import Theorems.Thm_PowerSeries_eq_of_forall_tsum_coeff_mul_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_taylorShift_mul

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace PowerSeries
p2m_export "PowerSeries" "mk coeff tsum_coeff_mul_mul_pow_eq_of_norm_lt norm_coeff_mul_mul_pow_le norm_coeff_taylorShift_mul_pow_le tsum_coeff_taylorShift_mul_pow_eq eq_of_forall_tsum_coeff_mul_pow_eq"
p2m_open "PowerSeries"

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

end PowerSeries

open _root_.PowerSeries _root_.P2MW.S_PowerSeries_taylorShift_mul.PowerSeries in

theorem solution {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (a : L) (ha : ‖a‖ < ρ) :
    (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) (F * G) * ((n + k).choose n : L) * a ^ k)
      = (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)
        * (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) G * ((n + k).choose n : L) * a ^ k) := by

  have hFG : ∀ n, ‖PowerSeries.coeff n (F * G)‖ * ρ ^ n ≤ M * M' := norm_coeff_mul_mul_pow_le F G hρ.le hF hG
  have hSFG := fun n => (norm_coeff_taylorShift_mul_pow_le (F * G) hρ hFG a ha n).2
  have hSF := fun n => (norm_coeff_taylorShift_mul_pow_le F hρ hF a ha n).2
  have hSG := fun n => (norm_coeff_taylorShift_mul_pow_le G hρ hG a ha n).2
  have hprod := norm_coeff_mul_mul_pow_le _ _ hρ.le hSF hSG
  refine eq_of_forall_tsum_coeff_mul_pow_eq _ _ hρ hSFG hprod (fun b hb => ?_)
  rw [tsum_coeff_mul_mul_pow_eq_of_norm_lt _ _ hρ hSF hSG b hb,
    tsum_coeff_taylorShift_mul_pow_eq (F * G) hρ hFG a ha b hb,
    tsum_coeff_taylorShift_mul_pow_eq F hρ hF a ha b hb,
    tsum_coeff_taylorShift_mul_pow_eq G hρ hG a ha b hb]
  have hab : ‖a + b‖ < ρ := lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)
  exact tsum_coeff_mul_mul_pow_eq_of_norm_lt F G hρ hF hG (a + b) hab

#print axioms solution

end S_PowerSeries_taylorShift_mul
end P2MW
export P2MW.S_PowerSeries_taylorShift_mul (solution)
