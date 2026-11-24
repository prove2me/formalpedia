-- Prove2me | solution 1 for ReciprocityTheory.Cheb.Smooth.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:54.648908+00:00
-- url     : https://prove2.me/submissions/78ce43a6-f157-4201-9ba5-d66d19a4f937

import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFin
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
namespace Smooth
theorem _root_.solution {E : Type} [Field E] [NumberField E] {S T : Finset (Prm E)} {a : Ideal (𝓞 E)}
    (h : Smooth S a) (hST : S ⊆ T) : Smooth T a := fun q hq => hST (h q hq)
end Smooth
end ReciprocityTheory.Cheb
