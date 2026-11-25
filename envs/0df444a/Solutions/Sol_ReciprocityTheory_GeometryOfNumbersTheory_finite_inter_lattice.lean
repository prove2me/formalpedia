-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.finite_inter_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:25.804487+00:00
-- url     : https://prove2.me/submissions/894429d8-80b3-4db3-93b5-3451f03ca87f

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_CountZSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Module
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (S : Set E)
    (hb : Bornology.IsBounded S) : (S ∩ (L : Set E)).Finite := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  haveI : DiscreteTopology L.toAddSubgroup := ‹DiscreteTopology L›
  have hc : IsClosed (L : Set E) := AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  exact Metric.finite_isBounded_inter_isClosed ⟨(‹DiscreteTopology L› : DiscreteTopology L)⟩ hb hc
end ReciprocityTheory.GeometryOfNumbersTheory
