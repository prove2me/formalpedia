-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.mem_divSupp_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:31.944838+00:00
-- url     : https://prove2.me/submissions/3bef4387-80aa-4225-bcfa-c7fcc6c1fdf8

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
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution {V W : Ideal (MRingOver F ι)} {f g : MRingOver F ι}
    (hW : W ∈ divSupp V (f * g)) (hf : f ∈ W) : W ∈ divSupp V f :=
  ⟨⟨⟨hW.1.1.1, sup_le (le_sup_left.trans hW.1.1.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩,
    fun Q hQ hQW => hW.1.2 ⟨hQ.1, (sup_span_mul_le V f g).trans hQ.2⟩ hQW⟩, hW.2⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1
