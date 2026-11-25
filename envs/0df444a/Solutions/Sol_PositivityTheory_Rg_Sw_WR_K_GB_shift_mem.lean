-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.shift_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:18.621731+00:00
-- url     : https://prove2.me/submissions/1e3c09ab-e077-4f45-a9ab-e19a29e168ba

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBCauchy
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_shift_apply

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
theorem _root_.solution (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) (i j : Fin n) {w : ℂ}
    (hw : ‖w‖ ≤ r i j) : b + w • Matrix.single i j (1 : ℂ) ∈ pdisc b r := by
  intro a c
  rw [shift_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact hw
  · simpa using (hr a c).le
end PositivityTheory.Rg.Sw.WR.K.GB
