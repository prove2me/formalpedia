-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_gram_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:02.527897+00:00
-- url     : https://prove2.me/submissions/e72ec845-14b1-4a7f-89e1-f45f442e74c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstAdapt
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
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} (X J Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Xᴴ * J * Y) a b = ∑ s, ∑ r, star (X r a) * J r s * Y s b := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
end PI.ScMuExists.UnitaryGroupMassFormula
