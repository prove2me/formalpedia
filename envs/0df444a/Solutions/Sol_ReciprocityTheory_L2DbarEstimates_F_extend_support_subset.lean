-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.extend_support_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:39.948555+00:00
-- url     : https://prove2.me/submissions/b88b8d92-a0c2-4453-ac4d-16dfebd79685

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Extend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {n : ℕ} {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (q : M)
    (hq : e.source.indicator (G ∘ e) q ≠ 0) : q ∈ e.symm '' tsupport G := by
  have hq' : q ∈ e.source := by
    by_contra h; exact hq (Set.indicator_of_notMem h _)
  rw [Set.indicator_of_mem hq'] at hq
  exact ⟨e q, subset_tsupport _ hq, e.left_inv hq'⟩
end ReciprocityTheory.L2DbarEstimates.F
