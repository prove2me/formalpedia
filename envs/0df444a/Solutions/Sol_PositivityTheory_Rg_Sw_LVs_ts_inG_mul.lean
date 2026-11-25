-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.ts_inG_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:01.020397+00:00
-- url     : https://prove2.me/submissions/94f659cb-2bdd-4a61-bdb8-cbba40185bfb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_IsSingTest
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TsContinuousNU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {g h : M2 n} (hg : InG g) (hh : InG h) : InG (g * h) := by
  unfold InG at *
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * JJ n * (g * h) = hᴴ * (gᴴ * JJ n * g) * h := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hg, hh]
end PositivityTheory.Rg.Sw.LVs
