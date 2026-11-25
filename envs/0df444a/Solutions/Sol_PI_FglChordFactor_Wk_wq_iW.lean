-- Prove2me | solution 1 for PI.FglChordFactor.Wk.wq_iW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:13.772932+00:00
-- url     : https://prove2.me/submissions/e07e6d23-ca8e-4559-9626-67d9183c2f1d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstPairSecondVariable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Theorems.Thm_PI_FglChordFactor_Wk_iW_mul_D
import Theorems.Thm_PI_FglChordFactor_Wk_iW_const
import Theorems.Thm_PI_FglChordFactor_Wk_hasSubst_iW
import Theorems.Thm_PI_FglChordFactor_Wk_subst_isWq
import Theorems.Thm_PI_FglChordFactor_Wk_fix_unique
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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (iW W wq) wq = wq * Dser W wq ^ 2 := by
  have hw : wq = 1 + cP W.a₁ * PowerSeries.X * wq + cP W.a₂ * PowerSeries.X ^ 2 * wq +
      cP W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 + cP W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      cP W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := h
  refine fix_unique (a₁ := W.a₁) (a₂ := W.a₂) (a₃ := W.a₃) (a₄ := W.a₄) (a₆ := W.a₆) (iW_const W wq) ?_ ?_
  · exact subst_isWq (hasSubst_iW W wq) h
  · have e := iW_mul_D W wq
    generalize iW W wq = i at e ⊢
    generalize hDdef : Dser W wq = D at e ⊢
    have hD : D = 1 - (cP W.a₁ * PowerSeries.X + cP W.a₃ * PowerSeries.X ^ 3 * wq) := hDdef.symm
    linear_combination (-(cP W.a₁) * wq * D - cP W.a₂ * wq * (i * D - PowerSeries.X)
      - cP W.a₃ * wq ^ 2 * D * ((i * D) ^ 2 - i * D * PowerSeries.X + PowerSeries.X ^ 2)
      - cP W.a₄ * wq ^ 2 * ((i * D) ^ 3 - (i * D) ^ 2 * PowerSeries.X + i * D * PowerSeries.X ^ 2 - PowerSeries.X ^ 3)
      - cP W.a₆ * wq ^ 3 * ((i * D) ^ 5 - (i * D) ^ 4 * PowerSeries.X + (i * D) ^ 3 * PowerSeries.X ^ 2
          - (i * D) ^ 2 * PowerSeries.X ^ 3 + i * D * PowerSeries.X ^ 4 - PowerSeries.X ^ 5)) * e
      + hw + wq * (D + 1) * hD
end PI.FglChordFactor.Wk
