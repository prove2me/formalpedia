-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_hermLine_eq_of_9e6d78ade988
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:13.259938+00:00
-- url     : https://prove2.me/submissions/b001924c-d8ec-45d4-8443-f244a4ca81b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl
end GroundTheory.Heights₂.Heights.Inter
