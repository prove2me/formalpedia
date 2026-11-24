-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integral_of_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:28.919815+00:00
-- url     : https://prove2.me/submissions/1846fea7-de64-4609-b8f0-e745b4bf0318

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgGauss
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {e U G : PowerSeries K} (he : IntegralPS e) (he0 : constantCoeff e = 0)
    (hU : IntegralPS U) (hU0 : constantCoeff U = 1) (h : e ^ 2 = X ^ 2 * U * G) : IntegralPS G := by
  obtain ⟨e', rfl⟩ := (PowerSeries.X_dvd_iff).mpr he0
  have he' : IntegralPS e' := fun n => by
    have := he (n + 1)
    rwa [coeff_succ_X_mul] at this
  have h2 : e' ^ 2 = U * G := by
    have hX : (X : PowerSeries K) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [← mul_assoc, ← h]
    ring
  have hUi : IntegralPS U⁻¹ := integralPS_inv hU (by rw [hU0, norm_one])
  have hG : G = U⁻¹ * e' ^ 2 := by
    rw [h2, ← mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [hU0]; exact one_ne_zero), one_mul]
  rw [hG]
  exact integralPS_mul hUi (integralPS_pow he' 2)
end ReciprocityTheory.ChartRestriction.L1
