-- Prove2me | solution 1 for PI.TwNormLat.W.intAt_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:44.230585+00:00
-- url     : https://prove2.me/submissions/76c6ee95-0f74-4e99-aae1-0d48f0bab0a9

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Theorems.Thm_PI_TwNormLat_W_intAt_add
import Theorems.Thm_PI_TwNormLat_W_intAt_neg

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
theorem _root_.solution {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  rw [sub_eq_add_neg]
  exact PI.TwNormLat.W.intAt_add P ha (PI.TwNormLat.W.intAt_neg P hb)
end PI.TwNormLat.W
