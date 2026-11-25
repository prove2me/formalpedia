-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.embOn_mul_embOn_disj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:49:04.466261+00:00
-- url     : https://prove2.me/submissions/3cb1faf2-a573-425e-b997-7788398793d1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {s t : Finset (Fin n)} (hst : ∀ c, c ∈ s → c ∉ t) (T : Matrix s s ℂ) (S : Matrix t t ℂ) :
    embOn s T * embOn t S = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.zero_apply, embOn]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1 : a ∈ s ∧ c ∈ s
  · by_cases h2 : c ∈ t ∧ b ∈ t
    · exact absurd h2.1 (hst c h1.2)
    · rw [dif_neg h2, mul_zero]
  · rw [dif_neg h1, zero_mul]
end PositivityTheory.Rg.Sw.LVs
