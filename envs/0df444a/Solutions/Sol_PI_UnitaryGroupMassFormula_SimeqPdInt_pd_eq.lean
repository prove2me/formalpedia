-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SimeqPdInt.pd_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:43:26.078863+00:00
-- url     : https://prove2.me/submissions/f9d1182d-a02c-41cf-b466-4925e270e513

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SimeqPdInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialCoefficientSeries_CoeffExpMvEqTs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SimeqPdInt
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.UnitaryGroupMassFormula.SimeqPdInt
theorem _root_.solution [DecidableEq σ] (k : σ) (F : MvPowerSeries σ ℂ_[p]) :
    PI.SimeqPdInt.pd k F = pderiv ℂ_[p] k F := by
  ext n
  rw [coeff_pderiv]
  change ((n k : ℂ_[p]) + 1) * coeff (n + Finsupp.single k 1) F = _
  ring
end PI.UnitaryGroupMassFormula.SimeqPdInt
