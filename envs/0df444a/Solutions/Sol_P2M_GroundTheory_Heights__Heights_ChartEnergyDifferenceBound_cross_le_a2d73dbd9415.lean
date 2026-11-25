-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyDifferenceBound_cross_le_a2d73dbd9415
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:21.726949+00:00
-- url     : https://prove2.me/submissions/87b36410-4d9a-4fdb-85a3-8a55be061687

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDiffEnergy

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
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyDifferenceBound
namespace GroundTheory.Heights₂.Heights.ChartEnergyDifferenceBound
theorem _root_.solution {u U χ a p G : ℝ} (hU : |u| ≤ U) (hχ : 0 ≤ χ) (hp : 0 ≤ p) (hG : 0 ≤ G)
    (ha : |a| ≤ Real.sqrt p * Real.sqrt G) :
    -(u * (χ * a + χ * a)) ≤ 2 * U ^ 2 * p + χ * χ * G / 2 := by
  have hsp := Real.sq_sqrt hp
  have hsG := Real.sq_sqrt hG
  have h0 : 0 ≤ |u| := abs_nonneg u
  have hua : -(u * a) ≤ |u| * |a| := by
    rw [← abs_mul]
    exact neg_le_abs _
  have h1 : -(u * (χ * a + χ * a)) ≤ 2 * χ * (|u| * |a|) := by
    nlinarith [mul_le_mul_of_nonneg_left hua hχ]
  have hb : |u| * |a| ≤ U * (Real.sqrt p * Real.sqrt G) := mul_le_mul hU ha (abs_nonneg a) (h0.trans hU)
  have h2 : 2 * χ * (|u| * |a|) ≤ 2 * χ * (U * (Real.sqrt p * Real.sqrt G)) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have h3 : 2 * χ * (U * (Real.sqrt p * Real.sqrt G)) ≤ 2 * U ^ 2 * p + χ * χ * G / 2 := by
    nlinarith [sq_nonneg (2 * U * Real.sqrt p - χ * Real.sqrt G)]
  linarith
end GroundTheory.Heights₂.Heights.ChartEnergyDifferenceBound
