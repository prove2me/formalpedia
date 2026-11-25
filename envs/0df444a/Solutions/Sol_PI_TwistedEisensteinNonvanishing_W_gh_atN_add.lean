-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.gh_atN_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:19.928662+00:00
-- url     : https://prove2.me/submissions/1db371bb-53e7-4c79-aaa9-6f49a2b9df54

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
theorem _root_.solution {N : ℕ} (v w : Fin N → E) (i : ℕ) : atN (v + w) i = atN v i + atN w i := by
  unfold atN
  split_ifs <;> simp
end PI.TwistedEisensteinNonvanishing.W
