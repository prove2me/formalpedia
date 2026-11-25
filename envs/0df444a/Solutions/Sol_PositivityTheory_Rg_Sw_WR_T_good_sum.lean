-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.good_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:25:59.554405+00:00
-- url     : https://prove2.me/submissions/ef43e898-14cd-42e2-a9fd-1b3acb24ad87

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_FD_sum

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
theorem _root_.solution {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, Good (F i)) :
    Good (fun y => ∑ i ∈ s, c i * F i y) := by
  refine ⟨?_, fun L => ?_⟩
  · exact ContDiff.sum fun i hi => contDiff_const.mul (hF i hi).1
  · rw [FD_sum s c F (fun i hi => (hF i hi).1) L]
    have : ∀ i ∈ s, ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖FD L (F i) y‖ ≤ h y := fun i hi => (hF i hi).2 L
    choose! h hint hb using this
    refine ⟨fun y => ∑ i ∈ s, ‖c i‖ * h i y, integrable_finset_sum s fun i hi => (hint i hi).const_mul _, fun y => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb i hi y) (norm_nonneg _)
end PositivityTheory.Rg.Sw.WR.T
