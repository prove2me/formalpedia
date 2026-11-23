-- Prove2me | solution 1 for PI.OneCosetSharp.W.lowProj_add_highProj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:22.733472+00:00
-- url     : https://prove2.me/submissions/8c329b03-6910-4eaa-80d3-dda4749a5e5b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent
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
theorem _root_.solution (v : Fin (n + c) → k) : (XP : (Fin (n + c) → k) →ₗ[k] _) v + AP v = v := by
  funext l
  rw [Pi.add_apply, lowProj_apply₂, projA_apply]
  by_cases h : l.1 < n <;> simp [h]
end PI.OneCosetSharp.W
