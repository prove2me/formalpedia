-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_analyticAt_eval_map_1ab986667e3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:57:26.012431+00:00
-- url     : https://prove2.me/submissions/8c476963-14a3-4275-a4cd-567970d0fa72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
theorem _root_.solution (p : MvPolynomial J ℤ) (z : J → ℂ) :
    AnalyticAt ℂ (fun y : J → ℂ => MvPolynomial.eval y (MvPolynomial.map (Int.castRingHom ℂ) p)) z := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.eval_C]
    exact analyticAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p v hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.eval_X]
    exact hp.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) v).analyticAt z)
end GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
