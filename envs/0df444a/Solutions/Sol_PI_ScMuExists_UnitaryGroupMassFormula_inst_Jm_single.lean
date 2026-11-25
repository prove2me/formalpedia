-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_Jm_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:34.72828+00:00
-- url     : https://prove2.me/submissions/1519b4b0-85e2-4f59-a443-2231985b4ca7

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (i : Fin n) :
    Formalism.REAL.Jm ε *ᵥ Pi.single i 1 = (if ε i then (1 : ℂ) else -1) • Pi.single i 1 := by
  funext r
  simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : r = i
  · subst h; simp
  · simp [h]
end PI.ScMuExists.UnitaryGroupMassFormula
