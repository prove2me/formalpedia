-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.piW_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:06.439614+00:00
-- url     : https://prove2.me/submissions/7f7bfa5c-7170-4994-b0c2-07f1f8260890

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_hJL_apply
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
variable {n r : ℕ} (ε : Fin n → Bool)
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (e f : Fin r → Fin n → ℂ) (z x : Fin n → ℂ) :
    piW ε e f z x = x - ∑ a, hJ ε (f a) x • e a - ∑ a, hJ ε (e a) x • f a -
      ((hJ ε z z)⁻¹ * hJ ε z x) • z := by
  simp [piW, hJL_apply, smul_eq_mul, mul_comm]
end PI.ScMuExists.UnitaryGroupMassFormula
