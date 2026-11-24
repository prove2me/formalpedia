-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:55.771246+00:00
-- url     : https://prove2.me/submissions/ee8296d2-9427-4f6b-abda-eb4286797689

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_length_locQuot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_length_quot_maximal

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
variable {R : Type*} [CommRing R]
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (W : Ideal (MRingOver R ι)) [hW : W.IsPrime] : multAt W W = 1 := by
  rw [multAt, dif_pos hW, inh_length_locQuot, inh_length_quot_maximal]
  rfl
end ReciprocityTheory.ChartRestriction.G.AI.I1
