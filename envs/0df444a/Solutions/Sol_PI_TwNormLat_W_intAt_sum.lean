-- Prove2me | solution 1 for PI.TwNormLat.W.intAt_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:15:23.763868+00:00
-- url     : https://prove2.me/submissions/4bcebb9b-8a46-4172-87de-2db746d2432a

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Theorems.Thm_PI_TwNormLat_W_intAt_zero
import Theorems.Thm_PI_TwNormLat_W_intAt_add

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (IntAt P) (fun _ _ ha hb => PI.TwNormLat.W.intAt_add P ha hb) (PI.TwNormLat.W.intAt_zero P) h
end PI.TwNormLat.W
