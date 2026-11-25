-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_tendsto_integral_outer_21be53af79a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:36:35.851544+00:00
-- url     : https://prove2.me/submissions/bd296c3d-030c-44c7-a9d2-8f63fe9948c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartIbpCutoff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_measurableSet_outer_6bc779b06f82
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_IsConeSetB_indicator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open ChartIntegrationByPartsSymmetry
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntegrationByPartsCutoff
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntegrationByPartsCutoff
theorem _root_.solution {g : (Fin (n + 1) → ℂ) → ℝ} (hg : Integrable g) :
    Tendsto (fun k : ℕ => ∫ y, (outer n k).indicator g y) atTop (𝓝 0) := by
  have h0 : (∫ _y : Fin (n + 1) → ℂ, (0 : ℝ)) = 0 := integral_zero _ _
  rw [← h0]
  refine tendsto_integral_of_dominated_convergence (fun y => ‖g y‖)
    (fun k => (hg.indicator (measurableSet_outer k)).aestronglyMeasurable) hg.norm
    (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · rw [Set.indicator]
    split_ifs
    · exact le_rfl
    · simp
  · obtain ⟨N, hN⟩ := exists_nat_gt (∑ i, ‖y i‖ ^ 2)
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun k hk => ?_
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    have : ¬ y ∈ outer n k := by
      simp only [outer, Set.mem_ofPred_eq, not_le]
      nlinarith
    simp [Set.indicator_of_notMem this]
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsCutoff
