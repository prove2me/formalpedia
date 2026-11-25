-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.mem_pdisc_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:05.558015+00:00
-- url     : https://prove2.me/submissions/3b4df2f9-7373-4ef6-a5ee-805628a0e681

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBCauchy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Metric
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) : b ∈ pdisc b r := by
  intro i j
  simp only [sub_self, norm_zero]
  exact (hr i j).le
end PositivityTheory.Rg.Sw.WR.K.GB
