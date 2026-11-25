-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.holo_prodFin_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:42.938899+00:00
-- url     : https://prove2.me/submissions/31c7d863-3b1a-4ec3-ac49-300410ae109e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (F : M × Fin p → ℂ) :
    Holo n (fun q : M × Fin p => z q.1) F ↔ ∀ i, Holo n z (fun x => F (x, i)) := by
  constructor
  · intro h i e he
    exact h (chartSlice e i) (isChart_chartSlice n z e he p i)
  · intro h E hE y hy
    obtain ⟨e, i, he, hye, hev⟩ := chart_prodFin_local n z hz p E hE y hy
    have h1 : DifferentiableAt ℂ ((fun x => F (x, i)) ∘ e.symm) y :=
      (h i e he).differentiableAt (e.open_target.mem_nhds hye)
    exact (h1.congr_of_eventuallyEq (hev.fun_comp F)).differentiableWithinAt
end ReciprocityTheory.L2DbarEstimates
