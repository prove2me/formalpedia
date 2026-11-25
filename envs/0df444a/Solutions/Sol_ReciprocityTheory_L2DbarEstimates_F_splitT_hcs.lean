-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.splitT_hcs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:31:28.242834+00:00
-- url     : https://prove2.me/submissions/07878cca-110b-41f1-a03a-3af271b94628

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
theorem _root_.solution {X : Type*} [Zero X] (u : M → X) (S : Fin n → Set M)
    (hS : ∀ j, IsCompact (S j)) (h : ∀ x, (∀ j, x ∉ S j) → u x = 0) : HasCompactSupport u := by
  refine HasCompactSupport.intro (K := ⋃ j, S j) (isCompact_iUnion hS) fun x hx => ?_
  exact h x fun j hj => hx (Set.mem_iUnion.2 ⟨j, hj⟩)
end ReciprocityTheory.L2DbarEstimates.F
