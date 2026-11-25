-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.rp3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:01.426063+00:00
-- url     : https://prove2.me/submissions/8f4267f7-4497-4f3f-b3af-89623200529d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousHerm

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.T
theorem _root_.solution {x : ℝ} (hx : 0 < x) (a b c : ℝ) : x ^ a * x ^ b * x ^ c = x ^ (a + b + c) := by
  rw [Real.rpow_add hx, Real.rpow_add hx]
end PositivityTheory.Rg.Sw.WR.T
