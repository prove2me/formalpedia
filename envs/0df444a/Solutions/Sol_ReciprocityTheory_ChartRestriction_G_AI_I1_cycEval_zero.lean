-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval_zero
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:12:47.842208+00:00
-- url     : https://prove2.me/submissions/03f29e4a-f5bf-45a0-a156-431b315d3d38

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
theorem _root_.solution (J : Ideal (MRingOver F ι) → ℤ) : cycEval J 0 = 0 := by
  first
    | (intros; simp [cycEval])
    | (intros; unfold cycEval; simp)
    | (intros; simp [cycEval]; done)
    | (intros; ext; simp [cycEval])
    | (intros; simp only [cycEval]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [cycEval])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [cycEval])
    | (intros; unfold cycEval; split_ifs <;> simp_all)
    | (intros; unfold cycEval; positivity)
    | (intros; unfold cycEval; ring)
    | (intros; unfold cycEval; exact?)
    | (intros; aesop (add norm simp [cycEval]))
    | (intros; simp [cycEval] <;> aesop)
    | (intros; exact cycEval.symm ..)
    | (intros; exact cycEval.comm ..)
  trace "HIT_18_0"

end 
