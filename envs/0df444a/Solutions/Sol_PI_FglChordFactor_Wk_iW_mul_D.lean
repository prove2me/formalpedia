-- Prove2me | solution 1 for PI.FglChordFactor.Wk.iW_mul_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:54.258783+00:00
-- url     : https://prove2.me/submissions/62341c57-504e-45ed-b1c9-949eb4866283

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstPairSecondVariable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Theorems.Thm_PI_FglChordFactor_Wk_D_const
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
theorem _root_.solution (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    iW W wq * Dser W wq = -PowerSeries.X := by
  have hc : PowerSeries.constantCoeff (Dser W wq) ≠ 0 := by rw [D_const]; exact one_ne_zero
  rw [iW, mul_assoc, PowerSeries.inv_mul_cancel _ hc, mul_one]
end PI.FglChordFactor.Wk
