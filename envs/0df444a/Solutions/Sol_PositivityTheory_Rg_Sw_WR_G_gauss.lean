-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:38.809484+00:00
-- url     : https://prove2.me/submissions/0f842be6-8c9f-44d9-8a18-447f24d86117

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousGramX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_HermTranspose
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ImportsAlt
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_integP
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_base
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_gauss_of
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_integP
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_rot
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_wick_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution : Gauss := gauss_of integP (wick_of integP) rot base
end PositivityTheory.Rg.Sw.WR.G
