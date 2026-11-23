-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.inf_comp_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:53.878424+00:00
-- url     : https://prove2.me/submissions/ed8c7561-6460-4580-9416-1fca4c445726

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
theorem _root_.solution (a : Ideles K) (w : InfinitePlace K) : (a : AdeleRing (𝓞 K) K).1 w ≠ 0 := by
  have h := congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w) a.mul_inv
  change (a : AdeleRing (𝓞 K) K).1 w * ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).1 w = 1 at h
  exact left_ne_zero_of_mul_eq_one h
end ReciprocityTheory.Neutral.Bridge.HCFR
