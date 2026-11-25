-- Prove2me | solution 1 for PI.SwSandwichOfWork.chartBwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:41.484871+00:00
-- url     : https://prove2.me/submissions/2c65b29e-4acf-4563-bc63-812fddabef1a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_ChartZeroEqOneOfLongWeylSq
import Theorems.Thm_PI_SwSandwichOfWork_Chart_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
namespace PI.SwSandwichOfWork
theorem _root_.solution : ChartBwdOf := by
  unfold ChartBwdOf ChartBwd
  intro hN hLog hW hBC hPF hPD hLW hEN hLI k r η hη
  obtain ⟨F, hF, hF0, hFη⟩ := Chart_core hN hLog hW hBC hPF hPD hLW hEN hLI k r
  obtain ⟨δ1, hδ1, hδ1'⟩ := hFη η hη
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (uH k r)
  let pr : Mat k r →L[ℝ] uH k r :=
    LinearMap.toContinuousLinearMap ((uH k r).linearProjOfIsCompl q hq)
  have hpr : ∀ (Y : Mat k r) (hY : Y ∈ uH k r), pr Y = ⟨Y, hY⟩ := fun Y hY =>
    Submodule.linearProjOfIsCompl_apply_left hq ⟨Y, hY⟩
  set f : Vs k r → uH k r := fun w => pr (F w) with hfdef
  have hf : HasStrictFDerivAt f (pr.comp ((Lm k r).comp (Vs k r).subtypeL)) 0 := by
    have h1 : HasStrictFDerivAt F (Lm k r) ((Vs k r).subtypeL (0 : Vs k r)) := by
      rw [map_zero]; exact hF
    exact pr.hasStrictFDerivAt.comp (0 : Vs k r) (h1.comp (0 : Vs k r) (Vs k r).subtypeL.hasStrictFDerivAt)
  have hf0 : f 0 = 0 := by
    show pr (F ((0 : Vs k r) : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r)) = 0
    rw [Submodule.coe_zero, hF0, map_zero]
  have hmap := hf.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr fun y => by
    obtain ⟨v, hv, hLv⟩ := (hLI k r).2.1 y y.2
    refine ⟨⟨v, hv⟩, ?_⟩
    change pr (Lm k r v) = y
    rw [hLv, hpr _ y.2])
  rw [hf0] at hmap
  have hρ : 0 < min η δ1 := lt_min hη hδ1
  have hS : f '' Metric.ball (0 : Vs k r) (min η δ1) ∈ 𝓝 (0 : uH k r) :=
    (congrArg (fun l => f '' Metric.ball (0 : Vs k r) (min η δ1) ∈ l) hmap).mp
      (Filter.image_mem_map (Metric.ball_mem_nhds _ hρ))
  obtain ⟨δ2, hδ2, hball⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨δ2, hδ2, fun Y hY hYn => ?_⟩
  have hYb : (⟨Y, hY⟩ : uH k r) ∈ Metric.ball (0 : uH k r) δ2 := by
    rw [mem_ball_zero_iff]; exact hYn
  obtain ⟨⟨v, hv⟩, hwS, hfw⟩ := hball hYb
  have hvn : ‖v‖ < min η δ1 := mem_ball_zero_iff.mp hwS
  obtain ⟨h1, h2, h3⟩ := hδ1' v hv (lt_of_lt_of_le hvn (min_le_right _ _))
  have hFY : F v = Y := by
    have h : pr (F v) = ⟨Y, hY⟩ := hfw
    rw [hpr _ h1] at h
    exact congrArg Subtype.val h
  refine ⟨v, hv, ?_, lt_of_lt_of_le hvn (min_le_left _ _), ?_⟩
  · rw [← hFY]; exact h2.symm
  · have h4 := norm_sub_norm_le (Lm k r v) (F v)
    rw [norm_sub_rev, hFY] at h4
    rw [hFY] at h3
    nlinarith [h3, h4]
end PI.SwSandwichOfWork
