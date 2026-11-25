-- Prove2me | solution 1 for PI.OneCosetSharp.W.projA_inX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:38.461405+00:00
-- url     : https://prove2.me/submissions/ce9311b3-a44f-448a-8dc0-a2e61a4cf5a4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent
import Theorems.Thm_PI_OneCosetSharp_W_projA_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE
variable {k : Type} [Field k] {n c : ℕ}
namespace PI.OneCosetSharp.W
theorem _root_.solution (v : Fin n → k) : (AP : (Fin (n + c) → k) →ₗ[k] _) (inX k n c v) = 0 := by
  funext l
  rw [projA_apply]
  by_cases h : l.1 < n
  · simp [h]
  · simp [h, PI.OneCosetSharp.Loc.inX]
end PI.OneCosetSharp.W
