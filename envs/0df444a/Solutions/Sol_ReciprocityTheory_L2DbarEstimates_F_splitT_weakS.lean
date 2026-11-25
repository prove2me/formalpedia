-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.splitT_weakS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:18:50.183331+00:00
-- url     : https://prove2.me/submissions/f7c176d5-572c-46d2-9c7f-6b6fe3c215d3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest

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
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (F G : M → V n) (hFG : F =ᵐ[vol n z] G) (σ : M → Fin n → Fin n → ℂ)
    (h : IsWeakS n z F σ) : IsWeakS n z G σ := by
  unfold IsWeakS at h ⊢
  intro φ hφ j k
  rw [← h φ hφ j k]
  refine integral_congr_ae ?_
  filter_upwards [hFG] with x hx
  rw [hx]
end ReciprocityTheory.L2DbarEstimates.F
