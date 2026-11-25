-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.count_idealFI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:24:49.750435+00:00
-- url     : https://prove2.me/submissions/ba82b95c-15fb-4c2a-a1c8-1f3753e2e612

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge.HCFR
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (a : Ideles K) :
    FractionalIdeal.count K v (idealFI K a) = ordAt K v a := FractionalIdeal.count_finprod K v (fun w => ordAt K w a) (ordAt_eventually K a)
end ReciprocityTheory.Neutral.Bridge.HCFR
