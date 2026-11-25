-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RegChartData_differentiableAt_u_245b9536963d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:44.87933+00:00
-- url     : https://prove2.me/submissions/c30ece8e-c426-4158-b015-17585424616d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PMollifiedNearSmooth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_isOpen_Yo_98ca97526c8d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_symm_mem_Yo_ad344fcd4555
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_contDiffAt_comp_symm_of_smoothOn_ea30a6a65011
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollify_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric
open scoped ContDiff
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' coordDiv limsupExt)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RegChartData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
  (R : RegChartData A)
namespace GroundTheory.Heights₂.Heights.Regular.RegChartData
theorem _root_.solution (j : Fin R.N) {y : Fin D → ℂ} (hy : y ∈ (R.chart j).target)
    (hyA : y ∉ coordDiv (R.S j)) : DifferentiableAt ℝ (R.u j) y := by
  have hq : ContDiffAt ℝ ∞ (R.q j) y :=
    (R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds hy)
  have hph := contDiffAt_comp_symm_of_smoothOn (R.compat j) R.isOpen_Yo R.ph_smooth
    (R.symm_mem_Yo j hy hyA) ((R.chart j).map_target hy)
  rw [(R.chart j).right_inv hy] at hph
  exact (hq.add hph).differentiableAt (by simp)
end GroundTheory.Heights₂.Heights.Regular.RegChartData
