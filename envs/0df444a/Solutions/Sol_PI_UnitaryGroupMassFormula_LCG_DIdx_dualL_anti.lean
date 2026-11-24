-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.DIdx.dualL_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:16:55.03173+00:00
-- url     : https://prove2.me/submissions/78d691d2-f7bf-4a84-b5b9-8ede11beac21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDual

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
open PI.UnitaryGroupMassFormula.LCG.DIdx
namespace PI.UnitaryGroupMassFormula.LCG.DIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {k : ℕ} {X Y : Submodule (𝓞 K) (Fin k → K)}
    (h : X ≤ Y) : dualL Y ≤ dualL X :=
  fun _ ht s hs => ht s (h hs)
end PI.UnitaryGroupMassFormula.LCG.DIdx
