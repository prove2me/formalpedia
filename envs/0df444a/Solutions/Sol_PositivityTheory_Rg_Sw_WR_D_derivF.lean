-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.derivF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:53:32.242219+00:00
-- url     : https://prove2.me/submissions/b51e19e9-5561-4b6c-b991-d4fc0bc67c3b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivF
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_derivF_of
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_algA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_intG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution : DerivF := derivF_of intG algA
end PositivityTheory.Rg.Sw.WR.D
