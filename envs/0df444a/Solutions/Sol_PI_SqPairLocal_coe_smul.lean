-- Prove2me | solution 1 for PI.SqPairLocal.coe_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:55.094881+00:00
-- url     : https://prove2.me/submissions/30ce8ec0-c73b-4acc-b414-cf0d12db67cb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution (r : 𝓞 E) (v : Fin N → E) : (r : E) • v = r • v := by
  first
  | rfl
  | (ext i; rfl)
  | (ext i; simp [Algebra.smul_def])
end PI.SqPairLocal
