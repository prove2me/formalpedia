-- Prove2me | solution 1 for PI.UG.W.star_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:32:33.800296+00:00
-- url     : https://prove2.me/submissions/fc994742-d00c-4416-a5d5-0fadeaa6ebe7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_StdLatEqSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UG PI.UG.W
namespace PI.UG.W
theorem _root_.solution (E : Type) [Field E] [NumberField E] [StarRing E] (r : 𝓞 E) :
    star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
  exact ⟨⟨star (algebraMap (𝓞 E) E r), (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom⟩, rfl⟩
end PI.UG.W
