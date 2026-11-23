-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.RB.finite_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:14.233806+00:00
-- url     : https://prove2.me/submissions/3ea11094-a347-446c-aaac-52ba3e3f1a9b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ReducedBasisStatement
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IndepOfFlag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace ReciprocityTheory.ChartRestriction.G.H1.RB
theorem _root_.solution [FiniteDimensional ℝ E] (X : Submodule ℤ E) [DiscreteTopology X] (R : ℝ) :
    (Metric.closedBall (0 : E) R ∩ (X : Set E)).Finite := by
  haveI : DiscreteTopology X.toAddSubgroup := ‹DiscreteTopology X›
  have hc : IsClosed (X : Set E) := AddSubgroup.isClosed_of_discrete (H := X.toAddSubgroup)
  have hdisc : IsDiscrete (X : Set E) := by
    first
    | exact ⟨‹DiscreteTopology X›⟩
    | exact isDiscrete_iff_discreteTopology.2 ‹DiscreteTopology X›
    | exact ‹DiscreteTopology X›
  exact Metric.finite_isBounded_inter_isClosed hdisc Metric.isBounded_closedBall hc
end ReciprocityTheory.ChartRestriction.G.H1.RB
