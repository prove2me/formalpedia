-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_homog_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:46.631714+00:00
-- url     : https://prove2.me/submissions/6b621542-3431-4765-b143-9234bf2e0544

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_homog_X_pow

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
theorem _root_.solution (p : Σ k, ι k) : IsMultiHomog (X p : MRingOver F ι) (Pi.single p.1 1) := by
  simpa using inh_homog_X_pow (F := F) p 1
end ReciprocityTheory.ChartRestriction.G.AI.I1
