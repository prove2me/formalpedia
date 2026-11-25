-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.evX_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:37:33.858253+00:00
-- url     : https://prove2.me/submissions/4924e5c3-2cdb-4d9a-9282-8a7e8b4d2865

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_EvXPderivPhiP
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_hasFDerivAt_evX


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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (P : PX m n) : Continuous (evX P) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_evX P x).continuousAt
end PositivityTheory.Rg.Sw.WR.G
