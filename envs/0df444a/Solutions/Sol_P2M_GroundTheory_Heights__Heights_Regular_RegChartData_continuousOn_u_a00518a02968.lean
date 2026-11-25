-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RegChartData_continuousOn_u_a00518a02968
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:57.066981+00:00
-- url     : https://prove2.me/submissions/4d19cc3a-8a3d-4365-8a9e-dd126e9f715c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_contDiffAt_comp_symm_of_smoothOn_ea30a6a65011
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_isOpen_Yo_98ca97526c8d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_symm_mem_Yo_ad344fcd4555

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
open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
open GroundTheory.Heights₂.Heights.Regular.RegChartData
variable (R : RegChartData A)
namespace GroundTheory.Heights₂.Heights.Regular.RegChartData
theorem _root_.solution (j : Fin R.N) :
    ContinuousOn (R.u j) ((R.chart j).target \ coordDiv (R.S j)) := by
  intro y hy
  have hq : ContinuousAt (R.q j) y :=
    ((R.q_smooth j).continuousOn).continuousAt ((R.chart j).open_target.mem_nhds hy.1)
  have hx : (R.chart j).symm y ∈ (R.chart j).source := (R.chart j).map_target hy.1
  have hph := contDiffAt_comp_symm_of_smoothOn (R.compat j) R.isOpen_Yo R.ph_smooth
    (R.symm_mem_Yo j hy.1 hy.2) hx
  rw [(R.chart j).right_inv hy.1] at hph
  exact (hq.add hph.continuousAt).continuousWithinAt
end GroundTheory.Heights₂.Heights.Regular.RegChartData
