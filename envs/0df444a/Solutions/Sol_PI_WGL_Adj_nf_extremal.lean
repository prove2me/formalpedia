-- Prove2me | solution 1 for PI.WGL.Adj.nf_extremal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:07:28.413045+00:00
-- url     : https://prove2.me/submissions/4feb7e72-65b0-461a-bf4d-71d14b6dfd82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.Adj
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.Adj
theorem _root_.solution {N : ℕ} (lam : DomWeight N) :
    normFock lam (extremal ℂ N lam) (extremal ℂ N lam) = 1 := by
  unfold normFock
  refine div_self ?_
  intro h0
  have := (den_pos lam).1
  rw [h0] at this; simp at this
end PI.WGL.Adj
