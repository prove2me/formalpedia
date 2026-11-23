-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_snd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:07.460909+00:00
-- url     : https://prove2.me/submissions/f02647d0-acd1-48ca-85a3-a5a5e1ad96ec

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge.HCFR
theorem _root_.solution (w : InfinitePlace K) (x : (w.Completion)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (infIdele K w x : AdeleRing (𝓞 K) K).2 v = 1 := rfl
end ReciprocityTheory.Neutral.Bridge.HCFR
