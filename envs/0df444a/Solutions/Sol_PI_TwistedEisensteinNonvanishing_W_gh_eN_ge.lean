-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.gh_eN_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:31.592593+00:00
-- url     : https://prove2.me/submissions/000ecfec-8e52-49b2-866d-df4fdd91921b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnfoldingMatrixFreeCoordinate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {N s : ℕ} (h : N ≤ s) : eN E N s = 0 := by
  funext l
  have := l.2
  simp only [eN, Pi.zero_apply]
  rw [if_neg (by omega)]
end PI.TwistedEisensteinNonvanishing.W
