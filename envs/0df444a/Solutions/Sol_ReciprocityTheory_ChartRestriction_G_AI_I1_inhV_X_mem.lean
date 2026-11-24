-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_X_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:53.063866+00:00
-- url     : https://prove2.me/submissions/19c96bda-c495-449a-a117-5c7f7d2d1b81

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {σ : Type*} (F : Type*) [Field F] [DecidableEq σ] (S : Finset σ)
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution {s : σ} (h : s ∈ S) : (X s : MvPolynomial σ F) ∈ inhV F S :=
  Ideal.subset_span ⟨s, h, rfl⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1
