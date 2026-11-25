-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.densOf3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:03:26.929993+00:00
-- url     : https://prove2.me/submissions/297f9196-7100-4f46-a63d-e64c9a024ed3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_CardAddB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousCexpIp
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensOf3
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_algA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_dens_of
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_derivF
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_intG
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_mollId


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution : Gauss → ClsGain → Integr → Dens := dens_of algA intG derivF mollId
end PositivityTheory.Rg.Sw.WR.D
