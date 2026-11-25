-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.Pw_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:56:28.538785+00:00
-- url     : https://prove2.me/submissions/7a0fa341-081a-4658-a26d-6cb0606ea468

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (c : ℂ) (x : Fin n → ℂ) : Pw ε e f (c • x) = c • Pw ε e f x := by
  simp only [Pw, hJ_smul, mul_smul, ← Finset.smul_sum, smul_sub]
end PI.NMeasInv.UnitaryGroupMassFormula
