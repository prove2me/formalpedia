-- Prove2me | solution 1 for PI.OneCosetSharp.W.lowProj_basisVec_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:10.194554+00:00
-- url     : https://prove2.me/submissions/7ef89a8c-a52f-4d1d-b8e6-f802980868ea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_GaStep
import Theorems.Thm_PI_OneCosetSharp_W_eN_apply
import Theorems.Thm_P2M_PI_OneCosetSharp_W_lowProj_apply__162d0f7a10c7


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
theorem _root_.solution (q : ℕ) (hq : n ≤ q) : (XP : (Fin (n + c) → k) →ₗ[k] _) (eN k (n + c) q) = 0 := by
  funext l
  rw [lowProj_apply₂, eN_apply]
  split_ifs <;> first | rfl | omega
end PI.OneCosetSharp.W
