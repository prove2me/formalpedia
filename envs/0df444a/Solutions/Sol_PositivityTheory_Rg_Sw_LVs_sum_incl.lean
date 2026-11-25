-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.sum_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:35.975097+00:00
-- url     : https://prove2.me/submissions/2f7ac585-d62d-4469-8ddc-5b6410295e18

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (s : Finset (Fin n)) (a : Fin n) (f : s → ℂ) :
    ∑ i : s, (if a = (i : Fin n) then (1 : ℂ) else 0) * f i = if h : a ∈ s then f ⟨a, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro i _ hi
      have : a ≠ (i : Fin n) := fun e => hi (Subtype.ext e.symm)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : a ≠ (i : Fin n) := fun e => h (e ▸ i.2)
    simp [this]
end PositivityTheory.Rg.Sw.LVs
