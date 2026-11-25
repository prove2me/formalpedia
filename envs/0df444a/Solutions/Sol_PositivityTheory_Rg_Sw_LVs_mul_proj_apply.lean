-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.mul_proj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:43.045672+00:00
-- url     : https://prove2.me/submissions/9e298069-dde2-4f58-a71f-fe4784921971

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual

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
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {m : Type} [Fintype m] (s : Finset (Fin n)) (X : Matrix m s ℂ) (d : m) (b : Fin n) :
    (X * proj s) d b = if h : b ∈ s then X d ⟨b, h⟩ else 0 := by
  simp only [proj, Matrix.mul_apply, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨b, h⟩]
    · simp
    · intro c _ hc
      rw [if_neg]
      intro hcb
      exact hc (Subtype.ext hcb)
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]
    rintro rfl
    exact h c.2
end PositivityTheory.Rg.Sw.LVs
