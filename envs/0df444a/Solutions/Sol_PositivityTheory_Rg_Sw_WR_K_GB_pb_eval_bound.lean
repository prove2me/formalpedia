-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_eval_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:09.125058+00:00
-- url     : https://prove2.me/submissions/2cc65650-0bc1-47d3-bf7b-f876f949da1b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution {ι : Type} (R : MvPolynomial ι ℂ) (B : ℝ) :
    ∃ C : ℝ, ∀ v : ι → ℂ, (∀ k, ‖v k‖ ≤ B) → ‖MvPolynomial.eval v R‖ ≤ C := by
  induction R using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, fun v _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨C1, h1⟩ := hp; obtain ⟨C2, h2⟩ := hq
    exact ⟨C1 + C2, fun v hv => by
      simp only [map_add]; exact (norm_add_le _ _).trans (add_le_add (h1 v hv) (h2 v hv))⟩
  | mul_X p k hp =>
    obtain ⟨C1, h1⟩ := hp
    exact ⟨max C1 0 * max B 0, fun v hv => by
      simp only [map_mul, MvPolynomial.eval_X, norm_mul]
      exact mul_le_mul ((h1 v hv).trans (le_max_left _ _)) ((hv k).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)⟩
end PositivityTheory.Rg.Sw.WR.K.GB
