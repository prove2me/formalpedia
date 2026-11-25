-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_isHomogeneous_of_isMultiHomog_one_269118ab0cfe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:45.259609+00:00
-- url     : https://prove2.me/submissions/f05405f3-163c-4a73-afc8-abd7af7d8870

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLineFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLinearQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHomogeneousOfIsMultiHomogOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
variable {F : Type} [Field F]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K₀ : Type} [Fintype K₀] {ι₀ : K₀ → Type}
    [∀ k, Fintype (ι₀ k)] (hK : Fintype.card K₀ = 1) {f : MRingOver F ι₀}
    (hf : IsMultiHomog f fun _ => 1) : f.IsHomogeneous 1 := by
  intro d hd
  have h := hf d (mem_support_iff.mpr hd)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_sigma]
  simp [h, hK]
end GroundTheory.Heights₂.Heights.Inter
