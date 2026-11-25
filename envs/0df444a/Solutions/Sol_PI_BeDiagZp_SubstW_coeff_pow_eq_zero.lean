-- Prove2me | solution 1 for PI.BeDiagZp.SubstW.coeff_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:21.364837+00:00
-- url     : https://prove2.me/submissions/e349946e-0619-44a8-a7b4-b56383c1f727

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear

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
open PI PI.BeDiagZp PI.BeDiagZp.SubstW
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.SubstW
theorem _root_.solution {σ : Type*} {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) {n : ℕ} {d : σ →₀ ℕ} (h : d.degree < n) :
    MvPowerSeries.coeff d (F ^ n) = 0 :=
  MvPowerSeries.coeff_of_lt_order
    ((Nat.cast_lt.mpr h).trans_le (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n hF))
end PI.BeDiagZp.SubstW
