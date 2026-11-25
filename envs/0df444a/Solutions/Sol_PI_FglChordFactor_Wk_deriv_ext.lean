-- Prove2me | solution 1 for PI.FglChordFactor.Wk.deriv_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:41:55.468741+00:00
-- url     : https://prove2.me/submissions/4438b761-6b5f-4c97-b30b-d26241b58ee7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstPairSecondVariable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Theorems.Thm_PI_AddIntG_Wk_inv_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS


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
open PI PI.FglChordFactor PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS inv_mem_SerS)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglChordFactor.Wk
theorem _root_.solution {f g : PowerSeries ℂ_[p]} (hd : PowerSeries.derivative ℂ_[p] f = PowerSeries.derivative ℂ_[p] g)
    (h0 : PowerSeries.constantCoeff f = PowerSeries.constantCoeff g) : f = g := by
  ext n
  rcases n with _ | n
  · simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
  · have e := congrArg (PowerSeries.coeff n) hd
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at e
    first
    | exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero n) e
    | exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) e
end PI.FglChordFactor.Wk
