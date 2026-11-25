-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.wdb_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:26:06.513641+00:00
-- url     : https://prove2.me/submissions/e9dc5838-e6c2-41b7-be87-e9224490daa2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wdb n j f =ᶠ[𝓝 x] wdb n j g := h.eventuallyEq_nhds.mono fun _ hy => wdb_congr hy
end ReciprocityTheory.L2DbarEstimates
