-- Prove2me | solution 1 for PI.PC.piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:18.244396+00:00
-- url     : https://prove2.me/submissions/b48c3f19-ba1a-4837-9c3d-e4ac996b63c8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact
import Theorems.Thm_PI_PC_phi_intervalIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real MeasureTheory Set
namespace PI.PC
theorem _root_.solution {p q c : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) (hc : 0 < c) (hcp : c ≤ log p) :
    ∫ t in p..q, phi t ≤ log 4 / c ^ 2 * (q - p) := by
  have hconst : ∀ t ∈ Icc p q, phi t ≤ log 4 / c ^ 2 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlogt : c ≤ log t := le_trans hcp (Real.log_le_log (by linarith) ht.1)
    have hlpos : 0 < log t := lt_of_lt_of_le hc hlogt
    have hθ : Chebyshev.theta t ≤ log 4 * t := Chebyshev.theta_le_log4_mul_x ht0.le
    have hθ0 : 0 ≤ Chebyshev.theta t := Chebyshev.theta_nonneg t
    have hl4 : 0 ≤ log 4 := Real.log_nonneg (by norm_num)
    have hc2 : c ^ 2 ≤ log t ^ 2 := pow_le_pow_left₀ hc.le hlogt 2
    unfold phi
    rw [div_le_div_iff₀ (mul_pos ht0 (pow_pos hlpos 2)) (pow_pos hc 2)]
    calc Chebyshev.theta t * c ^ 2 ≤ (log 4 * t) * log t ^ 2 :=
          mul_le_mul hθ hc2 (sq_nonneg c) (mul_nonneg hl4 ht0.le)
      _ = log 4 * (t * log t ^ 2) := by ring
  have hint_r : IntervalIntegrable (fun _ : ℝ => log 4 / c ^ 2) volume p q := intervalIntegrable_const
  calc ∫ t in p..q, phi t ≤ ∫ t in p..q, log 4 / c ^ 2 :=
        intervalIntegral.integral_mono_on hpq (phi_intervalIntegrable hp hpq) hint_r hconst
    _ = log 4 / c ^ 2 * (q - p) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
end PI.PC
