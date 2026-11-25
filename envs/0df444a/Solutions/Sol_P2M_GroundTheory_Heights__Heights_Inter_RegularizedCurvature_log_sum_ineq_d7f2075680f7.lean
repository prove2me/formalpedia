-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_sum_ineq_d7f2075680f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:33:14.256805+00:00
-- url     : https://prove2.me/submissions/f94451a3-ac59-4353-ad0d-c400b6d9f261

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
namespace GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
theorem _root_.solution {x x0 ε : ℝ} (hx : 0 < x) (hx0 : 0 < x0) (hε : 0 < ε) :
    Real.log (x0 + ε) - x0 / (x0 + ε) * Real.log x0 ≤
      Real.log (x + ε) - x0 / (x0 + ε) * Real.log x := by
  have hS : 0 < x0 + ε := by linarith
  have hl : 0 < x0 / (x0 + ε) := div_pos hx0 hS
  have hm : 0 < ε / (x0 + ε) := div_pos hε hS
  have hlm : x0 / (x0 + ε) + ε / (x0 + ε) = 1 := by
    rw [← add_div, div_self hS.ne']
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr (div_pos hx hx0))
    (Set.mem_Ioi.mpr one_pos) hl.le hm.le hlm
  have harg : x0 / (x0 + ε) * (x / x0) + ε / (x0 + ε) * 1 = (x + ε) / (x0 + ε) := by
    field_simp
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hconc
  rw [harg, Real.log_div (by linarith) hS.ne', Real.log_div hx.ne' hx0.ne'] at hconc
  nlinarith
end GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
