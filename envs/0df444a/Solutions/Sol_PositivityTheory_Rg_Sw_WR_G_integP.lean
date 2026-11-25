-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.integP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:26:03.493834+00:00
-- url     : https://prove2.me/submissions/1e921375-956e-462d-b028-12be01054548

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousGramX
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_integP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution : IntegP := GI.integP
end PositivityTheory.Rg.Sw.WR.G
