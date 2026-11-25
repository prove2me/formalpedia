-- Prove2me | solution 1 for PI.OneCosetSharp.W.projA_eq_self_of_projX_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:35.153863+00:00
-- url     : https://prove2.me/submissions/490b2f7a-99f1-46d9-88a9-31a2ca796c78

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_GaStep
import Theorems.Thm_PI_OneCosetSharp_W_lowProj_add_highProj


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
theorem _root_.solution {w : Fin (n + c) → k} (hw : (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0) : AP w = w := by
  have h := lowProj_add_highProj (n := n) (c := c) w
  rwa [hw, zero_add] at h
end PI.OneCosetSharp.W
