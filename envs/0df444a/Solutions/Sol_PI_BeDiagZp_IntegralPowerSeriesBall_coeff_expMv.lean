-- Prove2me | solution 1 for PI.BeDiagZp.IntegralPowerSeriesBall.coeff_expMv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:33.120417+00:00
-- url     : https://prove2.me/submissions/a3bc2b04-aca7-4ed6-9cf4-74c4d1f66ac3

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
theorem _root_.solution (f : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1), coeff α (f ^ n) / (n.factorial : ℂ_[p]) := rfl
end PI.BeDiagZp.IntegralPowerSeriesBall
