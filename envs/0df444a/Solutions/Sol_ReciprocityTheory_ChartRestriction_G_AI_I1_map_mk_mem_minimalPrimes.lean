-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.map_mk_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:49.024995+00:00
-- url     : https://prove2.me/submissions/a28abf74-16ce-4a42-a303-2bb8840fde85

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
theorem _root_.solution {V W : Ideal R} {f : R} (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) :
    W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by
  have e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
  exact ⟨W, hW, rfl⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1
