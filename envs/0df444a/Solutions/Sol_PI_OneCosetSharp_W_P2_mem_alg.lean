-- Prove2me | solution 1 for PI.OneCosetSharp.W.P2.mem_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:29.790778+00:00
-- url     : https://prove2.me/submissions/3ea3ca63-c35b-4fa8-8bad-c43d426dcf1b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_AllowColLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.OneCosetSharp PI.OneCosetSharp.Loc PI.OneCosetSharp.LocE
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.P2
variable {k : Type} [Field k]
variable {k₀ m t b : ℕ}
namespace PI.OneCosetSharp.W.P2
theorem _root_.solution {A : Matrix (Fin b) (Fin b) k} : A ∈ alg (k := k) k₀ m t b ↔ ∀ p q, A p q ≠ 0 → S k₀ m t b p.1 q.1 :=
  Iff.rfl
end PI.OneCosetSharp.W.P2
