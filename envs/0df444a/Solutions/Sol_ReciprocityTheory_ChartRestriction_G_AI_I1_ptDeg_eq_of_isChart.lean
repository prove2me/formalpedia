-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.ptDeg_eq_of_isChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:01.937327+00:00
-- url     : https://prove2.me/submissions/d67a64c1-0003-45e6-9c2c-6cbb1ce1893f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartSwap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isUnit_mk_chartIdeal_X


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
theorem _root_.solution {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) {i j : ∀ k, ι k}
    (hi : IsChart V i) (hj : IsChart V j) : ptDeg V i = ptDeg V j := by
  have hu : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, i k⟩)) := fun k =>
    isUnit_mk_chartIdeal_X hV j _ (hi k)
  have hv : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V i) (X ⟨k, j k⟩)) := fun k =>
    isUnit_mk_chartIdeal_X hV i _ (hj k)
  let e := AlgEquiv.ofAlgHom (chartSwap hV.1.2.1 i j hu) (chartSwap hV.1.2.1 j i hv)
    (chartSwap_comp hV.1.2.1 j i hv hu) (chartSwap_comp hV.1.2.1 i j hu hv)
  exact e.toLinearEquiv.finrank_eq
end ReciprocityTheory.ChartRestriction.G.AI.I1
