-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.cayley
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:07.349157+00:00
-- url     : https://prove2.me/submissions/d482df99-a803-4de4-9447-bebf2131765c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyK
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyG
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_Cayley
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cayley_of
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_equivar
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_kappaFin
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_reindex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : Cayley := cayley_of equivar reindex kappaFin
end PositivityTheory.Rg.Sw.LVs
