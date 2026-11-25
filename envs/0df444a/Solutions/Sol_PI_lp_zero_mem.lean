-- Prove2me | solution 1 for PI.lp_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:21:31.121551+00:00
-- url     : https://prove2.me/submissions/2be02e75-6d31-42be-b58b-969aa2e25d67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LpLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LinearProgramLowerBound_LpFeasibleLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI
open Finset
namespace PI
theorem _root_.solution (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (hD : ∀ s, 0 ≤ Ds s) :
    (0 : ℝ) ∈ lpFeasible l d Ds :=
  ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ _ _ => rfl, fun s => by simpa using hD s, by simp⟩
end PI
