-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.ordAt_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:47:16.805959+00:00
-- url     : https://prove2.me/submissions/ae08a51b-a168-4517-8be8-87f3d9722353

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (a : Ideles K) : ordAt K v a⁻¹ = -ordAt K v a := by
  have h := ordAt_mul K v a a⁻¹
  rw [mul_inv_cancel, ordAt_one] at h
  linarith
end ReciprocityTheory.Neutral.Bridge.HCFR
