-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.diag_single_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:50:45.054967+00:00
-- url     : https://prove2.me/submissions/ed6dee8c-7f91-4b1e-b780-ae5e397ad7a5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (u v : Fin n → ℂ) (r s : Fin n) (c : ℂ) :
    diagonal u * single r s c * diagonal v = single r s (u r * c * v s) := by
  ext i k
  rw [mul_diagonal, diagonal_mul, single_apply, single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    ring
  · simp
end PositivityTheory.Rg.Sw.LVs.TC
