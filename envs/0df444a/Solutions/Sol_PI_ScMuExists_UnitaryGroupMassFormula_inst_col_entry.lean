-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_col_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:06.686801+00:00
-- url     : https://prove2.me/submissions/656a4c4b-ab2b-492e-8593-30ac262906fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstPlace
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
theorem _root_.solution {n : ℕ} (m : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hm : m *ᵥ Pi.single i 1 = Pi.single i 1) (r : Fin n) : m r i = if r = i then 1 else 0 := by
  have := congrFun hm r
  simpa [Matrix.mulVec_single_one, Pi.single_apply] using this
end PI.ScMuExists.UnitaryGroupMassFormula
