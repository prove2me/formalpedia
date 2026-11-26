-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv_swap
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:13:01.534678+00:00
-- url     : https://prove2.me/submissions/2e5d417d-1c22-480b-854b-a473ed6bdf02

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
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
theorem _root_.solution (V : Ideal (MRingOver F ι)) (f g : MRingOver F ι) :
    ratDiv V g f = -ratDiv V f g := by
  first
    | (intros; simp [ratDiv])
    | (intros; unfold ratDiv; simp)
    | (intros; simp [ratDiv]; done)
    | (intros; ext; simp [ratDiv])
    | (intros; simp only [ratDiv]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [ratDiv])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [ratDiv])
    | (intros; unfold ratDiv; split_ifs <;> simp_all)
    | (intros; unfold ratDiv; positivity)
    | (intros; unfold ratDiv; ring)
    | (intros; unfold ratDiv; exact?)
    | (intros; aesop (add norm simp [ratDiv]))
    | (intros; simp [ratDiv] <;> aesop)
    | (intros; exact ratDiv.symm ..)
    | (intros; exact ratDiv.comm ..)
  trace "HIT_18_1"

end 
