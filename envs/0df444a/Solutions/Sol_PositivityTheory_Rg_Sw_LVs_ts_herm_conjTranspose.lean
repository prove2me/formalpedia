-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.ts_herm_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:42.906956+00:00
-- url     : https://prove2.me/submissions/a635a041-fa47-428d-af70-339664dae9d9

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
theorem _root_.solution (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  rw [conjTranspose_apply]
  apply Complex.ext <;> simp [herm] <;> ring
end PositivityTheory.Rg.Sw.LVs
