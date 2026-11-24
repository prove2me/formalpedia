-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.DetIdxW.vm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:15:44.575174+00:00
-- url     : https://prove2.me/submissions/5b40cf41-1ffd-474b-81ae-7a6a7f12f8b0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDet

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
open PI.UnitaryGroupMassFormula.LCG.DetIdxW
variable {K : Type} [Field K] [NumberField K] {k : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG.DetIdxW
theorem _root_.solution (M : Matrix (Fin k) (Fin k) K) (s : Fin k → K) : vm M s = s ᵥ* M := rfl
end PI.UnitaryGroupMassFormula.LCG.DetIdxW
