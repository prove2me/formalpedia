-- Prove2me | solution 1 for PI.WGL.Adj.nf_self_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:44.898168+00:00
-- url     : https://prove2.me/submissions/ee2e2887-b0be-4f96-b684-36326f4d80b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockPos
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
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    (normFock lam f f).im = 0 := by
  rw [nf_eq, Complex.div_ofReal_im]
  by_cases hf : f = 0
  · subst hf; simp [Formalism.REAL.fockF]
  · rw [(Formalism.GradedWeylDivisibility.fockPos _ f hf).2, zero_div]
end PI.WGL.Adj
