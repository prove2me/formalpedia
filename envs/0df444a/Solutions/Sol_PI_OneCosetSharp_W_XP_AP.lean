-- Prove2me | solution 1 for PI.OneCosetSharp.W.XP_AP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:42.936901+00:00
-- url     : https://prove2.me/submissions/8690768f-729e-4adc-9398-8f26c9cfe4f0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_GaStep
import Theorems.Thm_P2M_PI_OneCosetSharp_W_lowProj_apply__162d0f7a10c7
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
theorem _root_.solution (w : Fin (n + c) → k) : (XP : (Fin (n + c) → k) →ₗ[k] _) (AP w) = 0 := by
  funext l
  rw [lowProj_apply₂, projA_apply]
  split_ifs <;> rfl
end PI.OneCosetSharp.W
