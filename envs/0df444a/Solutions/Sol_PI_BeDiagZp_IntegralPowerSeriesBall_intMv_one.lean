-- Prove2me | solution 1 for PI.BeDiagZp.IntegralPowerSeriesBall.intMv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:10.888397+00:00
-- url     : https://prove2.me/submissions/7bad192f-5776-4eb1-a9fd-d9e8727fcf26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt

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
open PI.BeDiagZp.IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.BeDiagZp.IntegralPowerSeriesBall
theorem _root_.solution : IntegralMv (1 : MvPowerSeries σ ℂ_[p]) := fun n => by
  rw [coeff_one]; split_ifs
  · exact (ballSub p).one_mem
  · exact (ballSub p).zero_mem
end PI.BeDiagZp.IntegralPowerSeriesBall
