-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.chart_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:26:41.615922+00:00
-- url     : https://prove2.me/submissions/89dead24-917c-4ad2-ac2e-bcd56dfa9cf9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chart_isField

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
variable {W : Ideal (MRingOver F ι)}
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (hW : IsProjVarF W 0) {j : ∀ k, ι k} (hj : IsChart W j) :
    Module.Finite F (MRingOver F ι ⧸ chartIdeal W j) := by
  letI := (chart_isField hW hj).toField
  haveI : Algebra.FiniteType F (MRingOver F ι ⧸ chartIdeal W j) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F (chartIdeal W j))
      (Ideal.Quotient.mkₐ_surjective F _)
  exact finite_of_finite_type_of_isJacobsonRing F _
end ReciprocityTheory.ChartRestriction.G.AI.I1
