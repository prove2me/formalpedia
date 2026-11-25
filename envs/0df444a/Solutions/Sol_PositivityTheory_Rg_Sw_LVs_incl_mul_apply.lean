-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.incl_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:22.758534+00:00
-- url     : https://prove2.me/submissions/1cfb8ccc-c941-4de7-ad36-36d699f6b4cd

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
theorem _root_.solution {m : Type} [Fintype m] (s : Finset (Fin n)) (X : Matrix s m ℂ) (a : Fin n) (d : m) :
    (dp_incl s * X) a d = if h : a ∈ s then X ⟨a, h⟩ d else 0 := by
  simp only [dp_incl, Matrix.mul_apply, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro c _ hc
      rw [if_neg]
      intro hac
      exact hc (Subtype.ext hac.symm)
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]
    rintro rfl
    exact h c.2
end PositivityTheory.Rg.Sw.LVs
