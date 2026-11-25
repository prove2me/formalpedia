-- Prove2me | solution 1 for PI.FglChordFactor.Wk.subst_isWq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:43.258454+00:00
-- url     : https://prove2.me/submissions/9235be94-6df5-426b-b126-0a6db6718680

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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq t : PowerSeries ℂ_[p]} (ht : PowerSeries.HasSubst t)
    (h : IsWq W wq) :
    PowerSeries.subst t wq = 1 + cP W.a₁ * t * PowerSeries.subst t wq + cP W.a₂ * t ^ 2 * PowerSeries.subst t wq +
      cP W.a₃ * t ^ 3 * PowerSeries.subst t wq ^ 2 + cP W.a₄ * t ^ 4 * PowerSeries.subst t wq ^ 2 +
      cP W.a₆ * t ^ 6 * PowerSeries.subst t wq ^ 3 := by
  have h' : wq = 1 + cP W.a₁ * PowerSeries.X * wq + cP W.a₂ * PowerSeries.X ^ 2 * wq +
      cP W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 + cP W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      cP W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := h
  have hφ : ∀ f : PowerSeries ℂ_[p], PowerSeries.subst t f = PowerSeries.substAlgHom ht f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hX : PowerSeries.substAlgHom ht (PowerSeries.X : PowerSeries ℂ_[p]) = t := by
    rw [← hφ, PowerSeries.subst_X ht]
  conv_lhs => rw [h']
  simp only [hφ, map_add, map_mul, map_pow, map_one, AlgHom.commutes, hX]
end PI.FglChordFactor.Wk
