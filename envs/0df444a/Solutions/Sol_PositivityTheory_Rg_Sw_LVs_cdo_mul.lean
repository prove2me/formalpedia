-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.cdo_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:50:52.542789+00:00
-- url     : https://prove2.me/submissions/aa827f71-5afe-4091-a5aa-880ec6e61c97

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
theorem _root_.solution {ι κ μ' : Type} [Fintype ι] [Fintype κ] [Fintype μ'] {s : Set E} {M : E → Matrix ι κ ℂ}
    {N : E → Matrix κ μ' ℂ} (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s)
    (hN : ∀ i j, ContDiffOn ℂ ∞ (fun x => N x i j) s) : ∀ i j, ContDiffOn ℂ ∞ (fun x => (M x * N x) i j) s := by
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hM i k).mul (hN k j)
end PositivityTheory.Rg.Sw.LVs
