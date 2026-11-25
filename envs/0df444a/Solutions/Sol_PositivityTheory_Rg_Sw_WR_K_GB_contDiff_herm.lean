-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.contDiff_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:53:05.617854+00:00
-- url     : https://prove2.me/submissions/a32d86e5-a055-4f23-960f-d7b82ea2bc31

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_RatBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContDiffHerm

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
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (herm (n := n)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have hc : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : E n => ((x a b : ℝ) : ℂ)) := fun a b =>
    Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ b).comp (contDiff_apply ℝ (Fin n → ℝ) a))
  simp only [herm]
  push_cast
  exact (((hc i j).add (hc j i)).div_const 2).add ((contDiff_const.mul ((hc i j).sub (hc j i))).div_const 2)
end PositivityTheory.Rg.Sw.WR.K.GB
