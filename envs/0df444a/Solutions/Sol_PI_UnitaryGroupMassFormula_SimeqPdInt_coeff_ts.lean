-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SimeqPdInt.coeff_ts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:52:56.970742+00:00
-- url     : https://prove2.me/submissions/db0ac69b-7ac1-4983-a04c-24f11db8a25b

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
theorem _root_.solution (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) (a : σ →₀ ℕ) :
    coeff a (ts f N) = ∑ n ∈ Finset.range N, coeff a (f ^ n) / (n.factorial : ℂ_[p]) := by
  simp only [ts, map_sum, coeff_smul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]
end PI.UnitaryGroupMassFormula.SimeqPdInt
