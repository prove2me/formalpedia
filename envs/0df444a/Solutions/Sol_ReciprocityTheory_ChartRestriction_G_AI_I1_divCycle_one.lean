-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.divCycle_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:08.859814+00:00
-- url     : https://prove2.me/submissions/2146b182-ba72-40b8-8ccc-49368d14ac06

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero

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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (V : Ideal (MRingOver F ι)) : divCycle V (1 : MRingOver F ι) = 0 := by
  classical
  ext W
  have h : W ∉ divSupp V (1 : MRingOver F ι) := by
    rintro ⟨hW, -⟩
    rw [Ideal.span_singleton_one, sup_top_eq] at hW
    exact hW.1.1.ne_top (top_le_iff.mp hW.1.2)
  simp [divCycle, Finsupp.ofSupportFinite_coe, h]
end ReciprocityTheory.ChartRestriction.G.AI.I1
