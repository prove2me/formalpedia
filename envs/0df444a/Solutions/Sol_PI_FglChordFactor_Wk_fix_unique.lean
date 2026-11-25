-- Prove2me | solution 1 for PI.FglChordFactor.Wk.fix_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:01.411331+00:00
-- url     : https://prove2.me/submissions/0db5ccc5-6fa6-43d7-95fa-2bcac4bf9045

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
theorem _root_.solution {a₁ a₂ a₃ a₄ a₆ : ℂ_[p]} {t V₁ V₂ : PowerSeries ℂ_[p]} (ht : PowerSeries.constantCoeff t = 0)
    (h₁ : V₁ = 1 + cP a₁ * t * V₁ + cP a₂ * t ^ 2 * V₁ + cP a₃ * t ^ 3 * V₁ ^ 2 + cP a₄ * t ^ 4 * V₁ ^ 2 +
      cP a₆ * t ^ 6 * V₁ ^ 3)
    (h₂ : V₂ = 1 + cP a₁ * t * V₂ + cP a₂ * t ^ 2 * V₂ + cP a₃ * t ^ 3 * V₂ ^ 2 + cP a₄ * t ^ 4 * V₂ ^ 2 +
      cP a₆ * t ^ 6 * V₂ ^ 3) : V₁ = V₂ := by
  have key : (V₁ - V₂) * (1 - (cP a₁ * t + cP a₂ * t ^ 2 + cP a₃ * t ^ 3 * (V₁ + V₂) +
      cP a₄ * t ^ 4 * (V₁ + V₂) + cP a₆ * t ^ 6 * (V₁ ^ 2 + V₁ * V₂ + V₂ ^ 2))) = 0 := by
    linear_combination h₁ - h₂
  have hc : PowerSeries.constantCoeff (1 - (cP a₁ * t + cP a₂ * t ^ 2 + cP a₃ * t ^ 3 * (V₁ + V₂) +
      cP a₄ * t ^ 4 * (V₁ + V₂) + cP a₆ * t ^ 6 * (V₁ ^ 2 + V₁ * V₂ + V₂ ^ 2))) ≠ 0 := by
    simp [ht]
  rcases mul_eq_zero.1 key with h | h
  · exact sub_eq_zero.1 h
  · exact absurd (by rw [h, map_zero]) hc
end PI.FglChordFactor.Wk
