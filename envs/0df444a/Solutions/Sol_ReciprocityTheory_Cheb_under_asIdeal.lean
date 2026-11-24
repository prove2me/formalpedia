-- Prove2me | solution 1 for ReciprocityTheory.Cheb.under_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:22.376156+00:00
-- url     : https://prove2.me/submissions/10e7b791-4e48-41b2-b9ec-d21a84e1e860

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef

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
theorem _root_.solution {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (P : Prm E') : (under (E := E) P).asIdeal = P.asIdeal.under (𝓞 E) := rfl
end ReciprocityTheory.Cheb
