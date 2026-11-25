-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.piW_of_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:22:58.797772+00:00
-- url     : https://prove2.me/submissions/28fa8c52-4387-4422-a611-cb5309b5fd2b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_piW_apply
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
variable {ε}
variable {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {y : Fin n → ℂ} (he : ∀ a, hJ ε (e a) y = 0) (hf : ∀ a, hJ ε (f a) y = 0)
    (hz : hJ ε z y = 0) : piW ε e f z y = y := by
  rw [piW_apply]
  simp [he, hf, hz]
end PI.ScMuExists.UnitaryGroupMassFormula
