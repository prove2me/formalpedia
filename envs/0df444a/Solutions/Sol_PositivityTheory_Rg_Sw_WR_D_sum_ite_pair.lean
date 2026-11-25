-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.sum_ite_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:24.943838+00:00
-- url     : https://prove2.me/submissions/93bf563d-9eb2-49f4-8e3a-ccbac04b4745

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (k l : Fin n) (α : ℂ) (f : Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, (if a = k ∧ b = l then α else 0) * f a b = α * f k l := by
  rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha; simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h
end PositivityTheory.Rg.Sw.WR.D
