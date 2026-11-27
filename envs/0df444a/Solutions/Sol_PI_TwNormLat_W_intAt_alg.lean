-- Prove2me | solution 1 for PI.TwNormLat.W.intAt_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:17:57.104776+00:00
-- url     : https://prove2.me/submissions/7e68d2cf-6f6c-45e4-bf28-3ce88b32d90b

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Theorems.Thm_P2M_PI_TwNormLat_W_one_notMem__7f2d7b4a1758

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
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwNormLat.W
theorem _root_.solution (x : 𝓞 E) : IntAt P (algebraMap (𝓞 E) E x) :=
  ⟨x, 1, PI.TwNormLat.W.one_notMem' P, by simp⟩
end PI.TwNormLat.W
