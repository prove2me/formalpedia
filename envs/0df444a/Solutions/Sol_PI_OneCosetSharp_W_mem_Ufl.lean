-- Prove2me | solution 1 for PI.OneCosetSharp.W.mem_Ufl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:22.561278+00:00
-- url     : https://prove2.me/submissions/b2c98fbd-48f3-4633-8b55-b6b383f54ac2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent

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
theorem _root_.solution {i : ℕ} {v : Fin (n + c) → k} : v ∈ Ufl k n c i ↔ ∀ l : Fin (n + c), n + i ≤ l.1 → v l = 0 := by
  show (∀ l : Fin (n + c), l.1 ∉ {l | l < n + i} → v l = 0) ↔ _
  simp only [Set.mem_ofPred_eq, not_lt]
end PI.OneCosetSharp.W
