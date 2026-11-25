-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.cT_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:53.591045+00:00
-- url     : https://prove2.me/submissions/6d3659c3-2157-44e7-a535-170639e984dc

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_SylvesterLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Matrix
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT]
end PI.AutLzFinite.SlopeTestRemainingChoices
