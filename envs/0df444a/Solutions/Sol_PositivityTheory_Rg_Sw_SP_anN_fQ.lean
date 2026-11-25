-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.anN_fQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:25.862099+00:00
-- url     : https://prove2.me/submissions/c9c4d521-a08f-4aa9-8aa0-a5e916949317

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_Bridge
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_an_fQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s z : ℂ) (m : ℕ) (Q : Fm n) : AnalyticOnNhd ℂ (fQ s z m Q) (OmS s) := fun x hx => an_fQ s z m Q x hx
end PositivityTheory.Rg.Sw.SP
