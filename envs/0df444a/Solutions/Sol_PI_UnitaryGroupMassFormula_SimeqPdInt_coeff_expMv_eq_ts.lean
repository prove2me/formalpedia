-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SimeqPdInt.coeff_expMv_eq_ts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:01.184699+00:00
-- url     : https://prove2.me/submissions/dc5e8feb-3f20-4eae-824c-95650d1e482a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SimeqPdInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialCoefficientSeries_CoeffExpMvEqTs
import Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_coeff_ts
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_coeff_expMv_of_le


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
theorem _root_.solution {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0)
    {a : σ →₀ ℕ} {N : ℕ} (h : a.degree ≤ N) :
    coeff a (PI.FglGram.expMv f) = coeff a (ts f (N + 1)) := by
  rw [coeff_ts]
  exact PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.coeff_expMv_of_le hf N h
end PI.UnitaryGroupMassFormula.SimeqPdInt
