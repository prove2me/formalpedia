-- Prove2me | solution 1 for PI.TwNormLat.W.eN_eq_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:31:31.775903+00:00
-- url     : https://prove2.me/submissions/50d65d2d-4f2b-4479-bcef-ba9adadd81c6

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_CombinationEquivInvMemUnipotentFlagGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {K : Type} [Field K] {n : ℕ}
namespace PI.TwNormLat.W
theorem _root_.solution (l : Fin n) : Loc.eN K n l.1 = Pi.single l 1 := by
  funext m
  simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
end PI.TwNormLat.W
