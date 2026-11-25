-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_TayInvPow_main__b5d589cc85a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:19.431325+00:00
-- url     : https://prove2.me/submissions/1f2ad7e1-51b3-444f-a851-368bf4cf95f5

import Definitions.Def_Formalism_PeriodIntegrals_TayInvPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TaylorInversePower_SumMultinomialSub
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_coeff_F
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_F_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_L_mul_F

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TayInvPow
open MvPowerSeries
namespace PI.UnitaryGroupMassFormula.TayInvPow
namespace main
theorem _root_.solution.{u, v} : PI.TayInvPow.{u, v} := by
  intro σ A _ τ s t c hst hτ k β
  have hu : τ s * τ t = 1 := by rw [← map_mul, hst, map_one]
  have hpow : ∀ k, (τ s) ^ k * F c t k = 1 := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_mul, F_zero]
    | succ k ih => rw [pow_succ, mul_assoc, hτ, L_mul_F c s t hst k, ← hτ, ih]
  have hk : τ (t ^ k) = F c t k := by
    rw [map_pow]
    calc (τ t) ^ k = (τ t) ^ k * ((τ s) ^ k * F c t k) := by rw [hpow, mul_one]
      _ = (τ s * τ t) ^ k * F c t k := by rw [mul_pow]; ring
      _ = F c t k := by rw [hu, one_pow, one_mul]
  rw [hk, coeff_F]
  rfl
end main
end PI.UnitaryGroupMassFormula.TayInvPow
