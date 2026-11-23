-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.cdo_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:14.54435+00:00
-- url     : https://prove2.me/submissions/4dffc7b5-c61f-49ae-9a2c-d7175f3361d5

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
theorem _root_.solution {ι κ : Type} [Fintype ι] [Fintype κ] {s : Set E} {M : E → Matrix ι κ ℂ} :
    ContDiffOn ℂ ∞ M s ↔ ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s := by
  constructor
  · intro h i j
    have h1 : ContDiffOn ℂ ∞ (fun x => M x i) s := (contDiffOn_pi (Φ := fun x => (M x : ι → κ → ℂ))).1 h i
    exact (contDiffOn_pi (Φ := fun x => M x i)).1 h1 j
  · intro h
    exact (contDiffOn_pi (Φ := fun x => (M x : ι → κ → ℂ))).2 fun i =>
      (contDiffOn_pi (Φ := fun x => M x i)).2 fun j => h i j
end PositivityTheory.Rg.Sw.LVs
