-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.oneMom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:10:47.994998+00:00
-- url     : https://prove2.me/submissions/71d8185c-56f9-4f9e-8b50-d689c631eeea

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_oneMom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Real
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution : OneMom := Mom1.oneMom
end PositivityTheory.Rg.Sw.LC
