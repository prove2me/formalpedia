-- Prove2me | solution 1 for PI.BeDiagZp.simeq_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:04:00.919871+00:00
-- url     : https://prove2.me/submissions/d418aa10-bfa8-485c-88ac-284d30fdefb5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Theorems.Thm_PI_BeDiagZp_integral_expMv_neg

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
theorem _root_.solution {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq g f := by
  have e : g - f = -(f - g) := (neg_sub f g).symm
  refine ⟨by rw [e, map_neg, h.1, neg_zero], ?_⟩
  rw [e]; exact integral_expMv_neg h.1 h.2
end PI.BeDiagZp
