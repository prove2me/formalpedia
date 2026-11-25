-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.hsN_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:26.076618+00:00
-- url     : https://prove2.me/submissions/85d6b87a-6a19-4d2f-a721-7d1f78d86ac5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatCountAllOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN A := Real.sqrt_nonneg _
end PI.UnitaryGroupMassFormula.LCG
