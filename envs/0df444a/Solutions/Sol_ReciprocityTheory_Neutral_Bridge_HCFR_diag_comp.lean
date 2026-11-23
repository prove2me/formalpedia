-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.diag_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:37.87828+00:00
-- url     : https://prove2.me/submissions/8475600a-b25f-4a44-bc20-dfc71ba8c16a

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
theorem _root_.solution (k : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((diagUnits K k : AdeleRing (𝓞 K) K).2 v) = v.valuation K (k : K) := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : K)
end ReciprocityTheory.Neutral.Bridge.HCFR
