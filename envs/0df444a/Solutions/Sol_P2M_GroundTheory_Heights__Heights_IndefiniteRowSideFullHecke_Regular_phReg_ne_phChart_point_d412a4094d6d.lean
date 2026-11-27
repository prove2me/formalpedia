-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_phReg_ne_phChart_point_d412a4094d6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:12:59.91323+00:00
-- url     : https://prove2.me/submissions/ff78b61f-b08b-414d-b1bc-574ce7c49016

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_molli_fin_zero_de1edf9b11c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_IsCutoffFamily_ofPotentialCharts_4721dcb9cfaf
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli regMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts BoundedPshData pointReg pointCharts pointAtlas)
local notation "RegChartDataA" => GroundTheory.Heights₂.Heights.Regular.RegChartData
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
theorem _root_.solution (ρ : Mollifier 0) (t : ℝ) :
    pointReg.phReg ρ (-1) t (0 : Fin 1) () = 1 ∧
      (RegChartData.ofRegular pointReg pointOm pointOm_pot pointOm_pos).phChart pointReg.ph ρ t (0 : Fin 1) () = 0 := by
  constructor
  · simp [GroundTheory.Heights₂.Heights.Regular.RegChartData.phReg,
      GroundTheory.Heights₂.Heights.Regular.RegChartData.smoothed, molli_fin_zero,
      GroundTheory.Heights₂.Heights.Regular.RegChartData.trunc, limsupExt, coordDiv,
      GroundTheory.Heights₂.Heights.Regular.RegChartData.u, PotentialCharts.chartFun, pointReg, pointCharts]
  · simp [RegCharts.phChart, molli_fin_zero, RegCharts.u, RegChartData.ofRegular,
      RegCharts.ofPotentialCharts, pointReg, pointCharts]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
