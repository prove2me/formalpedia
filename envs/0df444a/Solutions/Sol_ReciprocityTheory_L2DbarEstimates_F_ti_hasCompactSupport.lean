-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.ti_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:29.570505+00:00
-- url     : https://prove2.me/submissions/7d46b54d-4aaa-426e-b1a7-f79926ee01ce

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_TestIneq

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (f : M → V n) (hf : IsTestForm n z f) : HasCompactSupport f := by
  have h : ∀ j, HasCompactSupport (fun x => f x j) := fun j => (hf j).2
  have hsub : Function.support f ⊆ ⋃ j, Function.support (fun x => f x j) := by
    intro x hx
    rw [Set.mem_iUnion]
    by_contra hne
    push_neg at hne
    apply hx
    ext j
    simpa [Function.mem_support] using hne j
  have hts : tsupport f ⊆ ⋃ j, tsupport (fun x => f x j) := by
    show closure (Function.support f) ⊆ ⋃ j, closure (Function.support fun x => f x j)
    rw [← closure_iUnion_of_finite]
    exact closure_mono hsub
  exact IsCompact.of_isClosed_subset (isCompact_iUnion fun j => h j) (isClosed_tsupport f) hts
end ReciprocityTheory.L2DbarEstimates.F
