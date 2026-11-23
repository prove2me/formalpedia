-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:55.015419+00:00
-- url     : https://prove2.me/submissions/4370dca5-8df9-4540-8bd4-b2c83de67db2

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
theorem _root_.solution (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    (infIdele K w x : AdeleRing (𝓞 K) K).1 w = x := by
  classical
  exact Pi.mulSingle_eq_same (M := fun v : InfinitePlace K => v.Completion) w (x : w.Completion)
end ReciprocityTheory.Neutral.Bridge.HCFR
