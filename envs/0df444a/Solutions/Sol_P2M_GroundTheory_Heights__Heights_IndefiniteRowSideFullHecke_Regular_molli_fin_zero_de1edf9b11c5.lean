-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_molli_fin_zero_de1edf9b11c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:20.617513+00:00
-- url     : https://prove2.me/submissions/8cfa814c-998e-4f47-8f93-39c446c65e5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
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
theorem _root_.solution (ρ : Mollifier 0) (t : ℝ) (f : (Fin 0 → ℂ) → ℝ) (z : Fin 0 → ℂ) :
    molli ρ t f z = f z := by
  have h : ∀ w : Fin 0 → ℂ, ρ.scaled t w * f (z - w) = ρ.toFun w * f z := by
    intro w
    rw [Subsingleton.elim (z - w) z]
    simp only [Mollifier.scaled, mul_zero, pow_zero, inv_one, one_mul]
    rw [Subsingleton.elim (t⁻¹ • w) w]
  unfold molli
  simp_rw [h]
  rw [integral_mul_const, ρ.integral_eq_one, one_mul]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
