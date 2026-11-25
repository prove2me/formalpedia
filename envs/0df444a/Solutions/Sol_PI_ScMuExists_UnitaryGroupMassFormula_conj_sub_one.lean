-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.conj_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:24:03.982309+00:00
-- url     : https://prove2.me/submissions/c2d860c7-e96d-4a3b-a0d5-0fa4b118592f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {h x h' : Matrix (Fin n) (Fin n) ℂ} (hh : h * h' = 1) :
    h * x * h' - 1 = h * (x - 1) * h' := by
  rw [mul_sub, sub_mul, mul_one, hh]
end PI.ScMuExists.UnitaryGroupMassFormula
