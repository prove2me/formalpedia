-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_mem_frameSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:21.968282+00:00
-- url     : https://prove2.me/submissions/44149c65-91c2-4c06-a591-e5d34132a4cb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstTop
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
open MeasureTheory NumberField Matrix
open scoped ENNReal Pointwise
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {I : Formalism.MainNotions.S.AutInst} {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (j : Fin r ⊕ Fin r ⊕ Unit) : instFvec e f z j ∈ frameSet I e f z := by
  rcases j with a | a | u <;> simp [instFvec, frameSet]
end PI.ScMuExists.UnitaryGroupMassFormula
