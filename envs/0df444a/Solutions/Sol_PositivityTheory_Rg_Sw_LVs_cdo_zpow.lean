-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.cdo_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:34.248229+00:00
-- url     : https://prove2.me/submissions/096b5ae1-e320-47e0-9f45-c15ef905b8b3

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
theorem _root_.solution {s : Set E} {f : E → ℂ} (hf : ContDiffOn ℂ ∞ f s) (h0 : ∀ x ∈ s, f x ≠ 0) (k : ℤ) :
    ContDiffOn ℂ ∞ (fun x => f x ^ k) s := by
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa only [zpow_natCast] using hf.pow j
  · refine ((hf.pow j).inv fun x hx => pow_ne_zero j (h0 x hx)).congr fun x _ => ?_
    simp [_root_.zpow_neg]
end PositivityTheory.Rg.Sw.LVs
