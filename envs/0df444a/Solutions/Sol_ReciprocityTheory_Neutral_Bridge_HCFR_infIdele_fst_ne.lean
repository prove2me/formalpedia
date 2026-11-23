-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:54.863822+00:00
-- url     : https://prove2.me/submissions/2a170aaa-c75b-45b0-9b67-96ee071112aa

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
theorem _root_.solution (w w' : InfinitePlace K) (h : w' ≠ w) (x : (w.Completion)ˣ) :
    (infIdele K w x : AdeleRing (𝓞 K) K).1 w' = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne (M := fun v : InfinitePlace K => v.Completion) h (x : w.Completion)
end ReciprocityTheory.Neutral.Bridge.HCFR
