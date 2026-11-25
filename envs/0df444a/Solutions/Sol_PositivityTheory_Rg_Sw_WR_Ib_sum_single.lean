-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.sum_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:15.774799+00:00
-- url     : https://prove2.me/submissions/07c4bfbb-2890-4b84-9875-1a675e0814ae

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Ib
theorem _root_.solution (β : E n) (c : ℂ) (k l : Fin n) :
    ∑ a, ∑ b, (β a b : ℂ) * (if a = k ∧ b = l then c else 0) = β k l * c := by
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    simp [ha]
  · simp
end PositivityTheory.Rg.Sw.WR.Ib
