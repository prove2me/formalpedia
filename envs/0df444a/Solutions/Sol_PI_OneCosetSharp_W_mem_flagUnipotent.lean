-- Prove2me | solution 1 for PI.OneCosetSharp.W.mem_flagUnipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:25.930636+00:00
-- url     : https://prove2.me/submissions/b461f7cb-9e13-4e81-85aa-d7e9b1b65282

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent
import Theorems.Thm_PI_OneCosetSharp_W_R1cond_symm

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
theorem _root_.solution {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) : r ∈ R1 k n c :=
  ⟨hr, R1cond_symm hr⟩
end PI.OneCosetSharp.W
