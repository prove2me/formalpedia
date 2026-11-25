-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval_eq_liftAddHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:03.726798+00:00
-- url     : https://prove2.me/submissions/6e01d296-f06d-4ef7-87a4-118b854073d5

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
theorem _root_.solution (J : Ideal (MRingOver F ι) → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval J D = Finsupp.liftAddHom (fun W => AddMonoidHom.mulRight (J W)) D := by
  rw [Finsupp.liftAddHom_apply]
  rfl
end ReciprocityTheory.ChartRestriction.G.AI.I1
