-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.mem_divSupp_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:09.843404+00:00
-- url     : https://prove2.me/submissions/dbfb8e7a-22f1-4a6c-8738-2de3a1e445b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_eq_of_le_of_mem_minimalPrimes

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
theorem _root_.solution {V W : Ideal (MRingOver F ι)} (hV : V.IsPrime) {f g : MRingOver F ι}
    (hgV : g ∉ V) (hW : W ∈ divSupp V f) : W ∈ divSupp V (f * g) := by
  refine ⟨⟨⟨hW.1.1.1, (sup_span_mul_le V f g).trans hW.1.1.2⟩, fun Q hQ hQW => ?_⟩, hW.2⟩
  have hfg : f * g ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rcases hQ.1.mem_or_mem hfg with hf | hg
  · exact hW.1.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩
      hQW
  · exact (eq_of_le_of_mem_minimalPrimes hV hW.1 hQ.1 (le_sup_left.trans hQ.2) hg hgV hQW).ge
end ReciprocityTheory.ChartRestriction.G.AI.I1
