-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.hJ_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:30:45.516833+00:00
-- url     : https://prove2.me/submissions/25c572bb-c86b-4c9f-bc59-931e77d55d7d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul

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
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  unfold hJ; rw [Matrix.mulVec_sub, dotProduct_sub]
end PI.NMeasInv.UnitaryGroupMassFormula
