-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.mem_minimalPrimes_sup_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:16.922025+00:00
-- url     : https://prove2.me/submissions/0ab31362-1249-4efd-befb-1286dfa7829b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp

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
open SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
theorem _root_.solution {V W Z : Ideal (MRingOver F ι)} {f t : MRingOver F ι}
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes)
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hWZ : W ≤ Z) :
    Z ∈ (W ⊔ Ideal.span {t}).minimalPrimes :=
  ⟨⟨hZ.1.1, sup_le hWZ (le_sup_right.trans hZ.1.2)⟩, fun _ ⟨hQ, hQle⟩ hQZ =>
    hZ.2 ⟨hQ, sup_le (hW.1.2.trans (le_sup_left.trans hQle)) (le_sup_right.trans hQle)⟩ hQZ⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
