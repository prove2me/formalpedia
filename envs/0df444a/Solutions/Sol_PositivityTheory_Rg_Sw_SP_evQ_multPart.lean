-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.evQ_multPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:31.719394+00:00
-- url     : https://prove2.me/submissions/591fdf94-405c-4f17-ba3a-8384a0dd56fb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeB
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_CC
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_C
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_yv
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_multPart_apply


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s z : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) (B : MC n) :
    evQ s z (multPart s m b k l Q) B = -(cB s b) * ((alB m b).eval z * vals s B (b, l, k) * evQ s z Q B) := by
  rw [multPart_apply, evQ_mul, evQ_CC, evQ_mul, evQ_mul, evQ_C, evQ_yv]
end PositivityTheory.Rg.Sw.SP
