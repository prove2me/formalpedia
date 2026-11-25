-- Prove2me | solution 1 for PI.BeDiagZp.integral_expMv_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:57:04.503199+00:00
-- url     : https://prove2.me/submissions/69e7da26-0dc4-4ac5-be64-0b55001c5c3c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Theorems.Thm_PI_BeDiagZp_IntegralPowerSeriesBall_intMv_inv
import Theorems.Thm_PI_BeDiagZp_expMv_add
import Theorems.Thm_PI_BeDiagZp_expMv_zero
import Theorems.Thm_PI_BeDiagZp_constantCoeff_expMv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp
open MvPowerSeries
open IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.BeDiagZp
theorem _root_.solution {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (h : IntegralMv (expMv x)) : IntegralMv (expMv (-x)) := by
  obtain ⟨G, hG, hG1⟩ := intMv_inv h (constantCoeff_expMv x)
  have hnx : constantCoeff (-x) = 0 := by rw [map_neg, hx, neg_zero]
  have hmul : expMv (-x) * expMv x = 1 := by rw [← expMv_add hnx hx, neg_add_cancel, expMv_zero]
  have : expMv (-x) = G := by
    calc expMv (-x) = expMv (-x) * (expMv x * G) := by rw [hG1, mul_one]
      _ = G := by rw [← mul_assoc, hmul, one_mul]
  rw [this]; exact hG
end PI.BeDiagZp
