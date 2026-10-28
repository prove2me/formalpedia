-- Prove2me | solution 1 for WeingartenCalc.Fundamental.integral_eq_averagingOperator_apply
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:30:32.033948+00:00
-- url     : https://prove2.me/submissions/79c2dda3-c521-481b-8bc6-b750a43e4f67

import Mathlib
import Definitions.Def_WeingartenCalc_Fundamental_TensorPower

open MeasureTheory Matrix

namespace WeingartenCalc.Fundamental

theorem tensorPow_cont {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin N) ℂ) (hU : Continuous U) (d : ℕ) (i j : Fin d → Fin N) :
    Continuous fun g => tensorPow U d g i j := by
  simp only [tensorPow, Matrix.of_apply]
  refine continuous_finsetProd _ fun x _ => ?_
  have h1 : Continuous fun g => (U g : Matrix (Fin N) (Fin N) ℂ) := continuous_subtype_val.comp hU
  exact (continuous_apply (j x)).comp ((continuous_apply (i x)).comp h1)

theorem avg_apply {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ) (i j : Fin d → Fin N) :
    averagingOperator μ U d i j = ∫ g, tensorPow U d g i j ∂μ := by
  letI : NormedAddCommGroup (Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ) :=
    Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ) := Matrix.normedSpace
  have hc : Continuous fun g => tensorPow U d g := by
    refine continuous_pi fun a => continuous_pi fun b => tensorPow_cont U hU d a b
  have hint := hc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  let L : Matrix (Fin d → Fin N) (Fin d → Fin N) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have := ContinuousLinearMap.integral_comp_comm L hint
  exact this.symm

end WeingartenCalc.Fundamental

open WeingartenCalc.Fundamental

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ)
    (i j : Fin d → Fin N) :
    ∫ g, ∏ x : Fin d, (U g : Matrix (Fin N) (Fin N) ℂ) (i x) (j x) ∂μ
      = averagingOperator μ U d i j :=
  (avg_apply μ U hU d i j).symm
