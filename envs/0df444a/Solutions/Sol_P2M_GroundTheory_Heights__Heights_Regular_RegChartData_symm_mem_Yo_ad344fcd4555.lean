-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RegChartData_symm_mem_Yo_ad344fcd4555
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:10.56343+00:00
-- url     : https://prove2.me/submissions/24d7dc4a-2de6-421e-b125-b8c4f88b3f7c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts

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
theorem _root_.solution (j : Fin R.N) {y : Fin D → ℂ} (hy : y ∈ (R.chart j).target)
    (hyA : y ∉ coordDiv (R.S j)) : (R.chart j).symm y ∈ R.Yo :=
  (R.mem_Yo j _ ((R.chart j).map_target hy)).2 (by rwa [(R.chart j).right_inv hy])
end GroundTheory.Heights₂.Heights.Regular.RegChartData
