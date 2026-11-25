-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hasCompactSupport_chartCutoff_663e8ce6ba54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:50:46.863948+00:00
-- url     : https://prove2.me/submissions/978c0bda-b268-4a28-b245-677847399cfa

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_eq_zero_29e9bf4eeaae

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
theorem _root_.solution (k : ℕ) : HasCompactSupport (chartCutoff (D := D) k) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) (2 * ((k : ℝ) + 1))) fun y hy => ?_
  apply chartCutoff_eq_zero
  have hr : (0 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by positivity
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr] at hy
  simp only [not_forall, not_le] at hy
  obtain ⟨i, hi⟩ := hy
  have h1 : ‖y i‖ ^ 2 ≤ ∑ j, ‖y j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 : (2 * ((k : ℝ) + 1)) ^ 2 ≤ ‖y i‖ ^ 2 := pow_le_pow_left₀ hr hi.le 2
  nlinarith [sq_nonneg ((k : ℝ) + 1)]
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
