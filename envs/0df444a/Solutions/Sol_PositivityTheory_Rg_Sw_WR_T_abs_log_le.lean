-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.abs_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:25.836612+00:00
-- url     : https://prove2.me/submissions/1725d9e8-ff7f-4378-be23-4a8ace00ee33

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
theorem _root_.solution (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) : |Real.log x| ≤ (x ^ δ + x ^ (-δ)) / δ := by
  have h1 : δ * Real.log x ≤ x ^ δ := by
    rw [← Real.log_rpow hx]
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx δ)
    linarith
  have h2 : -δ * Real.log x ≤ x ^ (-δ) := by
    rw [← Real.log_rpow hx]
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (-δ))
    linarith
  have p1 := Real.rpow_pos_of_pos hx δ
  have p2 := Real.rpow_pos_of_pos hx (-δ)
  rcases abs_cases (Real.log x) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h, le_div_iff₀ hδ] <;> nlinarith
end PositivityTheory.Rg.Sw.WR.T
