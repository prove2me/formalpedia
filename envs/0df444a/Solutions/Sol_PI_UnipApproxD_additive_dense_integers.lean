-- Prove2me | solution 1 for PI.UnipApproxD.additive_dense_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:15:48.13475+00:00
-- url     : https://prove2.me/submissions/c21b77b6-8e72-4a87-8584-08b50aaab264

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_denseRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnipApproxD
open NumberField IsDedekindDomain
namespace PI.UnipApproxD
theorem _root_.solution : AddDense := by
  intro F _ _
  exact IntegersDenseFiniteAdeles.denseRange
end PI.UnipApproxD
