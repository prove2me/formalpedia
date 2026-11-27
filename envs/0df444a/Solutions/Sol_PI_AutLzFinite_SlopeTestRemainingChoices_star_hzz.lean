-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.star_hzz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:14:33.556859+00:00
-- url     : https://prove2.me/submissions/5e22c8e8-cde9-4b51-86a9-52ff3f56cd99

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MjSmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
variable {S}
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution (z : S.V) : star (S.hT z z) = S.hT z z := by
  have h := S.herm.eq z z
  rwa [starRingEnd_apply] at h
end PI.AutLzFinite.SlopeTestRemainingChoices
