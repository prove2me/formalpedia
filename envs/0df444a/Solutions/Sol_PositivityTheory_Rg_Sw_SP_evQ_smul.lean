-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.evQ_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:48:49.210379+00:00
-- url     : https://prove2.me/submissions/88fe5086-34f5-4f97-b5fd-0320cbf9fdbf

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_Bridge
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_CC
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_evQ_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_smulC


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
theorem _root_.solution (s z a : ℂ) (P : Fm n) (B : MC n) : evQ s z (a • P) B = a * evQ s z P B := by
  rw [smulC, evQ_mul, evQ_CC]
end PositivityTheory.Rg.Sw.SP
