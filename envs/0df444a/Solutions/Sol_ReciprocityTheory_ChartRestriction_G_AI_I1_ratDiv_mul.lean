-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:21.952413+00:00
-- url     : https://prove2.me/submissions/93ecce82-4e4f-4a9e-a16e-bfa786551ed8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_divCycle_mul

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
theorem _root_.solution {V : Ideal (MRingOver F ι)} (hV : V.IsPrime) {f g f' g' : MRingOver F ι}
    (hf : f ∉ V) (hg : g ∉ V) (hf' : f' ∉ V) (hg' : g' ∉ V) :
    ratDiv V (f * f') (g * g') = ratDiv V f g + ratDiv V f' g' := by
  simp only [ratDiv, divCycle_mul hV hf hf', divCycle_mul hV hg hg',
    Finsupp.mapRange_add (hf := Nat.cast_zero) (fun a b => Nat.cast_add a b)]
  abel
end ReciprocityTheory.ChartRestriction.G.AI.I1
