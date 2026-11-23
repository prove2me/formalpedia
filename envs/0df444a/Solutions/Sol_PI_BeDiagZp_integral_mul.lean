-- Prove2me | solution 1 for PI.BeDiagZp.integral_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:58.281801+00:00
-- url     : https://prove2.me/submissions/62c670f4-0757-4ba3-95b8-26e0d140fe8f

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
open IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.BeDiagZp
theorem _root_.solution {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := fun n => by
  rw [coeff_mul]
  exact (ballSub p).sum_mem fun x _ => (ballSub p).mul_mem (hF x.1) (hG x.2)
end PI.BeDiagZp
