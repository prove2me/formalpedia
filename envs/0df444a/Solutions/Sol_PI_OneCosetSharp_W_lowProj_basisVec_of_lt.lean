-- Prove2me | solution 1 for PI.OneCosetSharp.W.lowProj_basisVec_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:17.307194+00:00
-- url     : https://prove2.me/submissions/c78b131d-3515-4e0f-b729-b4fa156d640e

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
theorem _root_.solution (q : ℕ) (hq : q < n) : (XP : (Fin (n + c) → k) →ₗ[k] _) (eN k (n + c) q) = eN k (n + c) q := by
  funext l
  rw [lowProj_apply₂, eN_apply]
  split_ifs <;> first | rfl | omega
end PI.OneCosetSharp.W
