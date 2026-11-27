-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:31.307974+00:00
-- url     : https://prove2.me/submissions/6fb92617-6640-4a12-9bd9-427cdcc8e0b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cycEval_eq_liftAddHom

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
theorem _root_.solution (J : Ideal (MRingOver F ι) → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ)
    (E : Ideal (MRingOver F ι) → Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval J (D.sum fun W m => m • E W) = cycEval (fun W => cycEval J (E W)) D := by
  rw [cycEval_eq_liftAddHom, map_finsuppSum]
  unfold cycEval
  refine Finsupp.sum_congr fun W _ => ?_
  rw [map_zsmul, smul_eq_mul, ← cycEval_eq_liftAddHom]
  rfl
end ReciprocityTheory.ChartRestriction.G.AI.I1
