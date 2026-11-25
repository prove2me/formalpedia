-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_linearForm_fin_one_eq_7c40a3c53653
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:47.339477+00:00
-- url     : https://prove2.me/submissions/375098de-d843-404a-9b41-ce2ecbc3a7c8

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
theorem _root_.solution {g : MvPolynomial (Fin 1) F} (hg : g.IsHomogeneous 1) :
    g = C (coeff (Finsupp.single 0 1) g) * X 0 := by
  ext d
  rw [coeff_C_mul, coeff_X]
  by_cases h : Finsupp.single 0 1 = d
  · subst h
    simp
  · rw [if_neg h, mul_zero]
    by_contra hne
    apply h
    have hw := hg hne
    refine Finsupp.ext fun i => ?_
    fin_cases i
    simp [Finsupp.weight_apply, Finsupp.sum_fintype] at hw ⊢
    omega
end GroundTheory.Heights₂.Heights.Inter
