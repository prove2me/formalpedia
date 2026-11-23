-- Prove2me | solution 1 for PI.BeDiagZp.ContPf.constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:11.457616+00:00
-- url     : https://prove2.me/submissions/cf46c2d8-ea7c-4f17-8dfc-310e89e812d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero

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
open PI PI.BeDiagZp PI.BeDiagZp.ContPf
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.ContPf
theorem _root_.solution {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (F : PowerSeries ℂ_[p]) (hF : PowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a F) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha F hF
end PI.BeDiagZp.ContPf
