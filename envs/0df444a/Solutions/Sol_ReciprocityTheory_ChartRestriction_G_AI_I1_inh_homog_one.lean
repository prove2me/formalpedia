-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_homog_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:40.618632+00:00
-- url     : https://prove2.me/submissions/5c4112cd-77e3-483a-9d53-b60250c76405

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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*}
  [Field F]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution : IsMultiHomog (1 : MRingOver F ι) 0 := by
  intro n hn k
  rw [support_one, Finset.mem_singleton] at hn
  subst hn
  simp
end ReciprocityTheory.ChartRestriction.G.AI.I1
