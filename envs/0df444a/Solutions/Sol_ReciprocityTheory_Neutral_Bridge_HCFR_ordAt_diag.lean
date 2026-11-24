-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.ordAt_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:47:16.131154+00:00
-- url     : https://prove2.me/submissions/22f45cd7-c632-497e-811f-87ec68b732f8

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_diag_comp

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
    ordAt K v (diagUnits K k) = -WithZero.log (v.valuation K (k : K)) := by
  unfold ordAt
  rw [diag_comp]
end ReciprocityTheory.Neutral.Bridge.HCFR
