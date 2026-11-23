-- Prove2me | solution 1 for PI.BeDiagZp.expMv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:58.012799+00:00
-- url     : https://prove2.me/submissions/d21f9b72-033e-4a17-8f67-cb14c08306ad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Theorems.Thm_PI_BeDiagZp_IntegralPowerSeriesBall_coeff_expMv

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
theorem _root_.solution : expMv (0 : MvPowerSeries σ ℂ_[p]) = 1 := by
  ext α
  rw [coeff_expMv, Finset.sum_range_succ']
  simp
end PI.BeDiagZp
