-- Prove2me | solution 1 for TierneyMH1998.maxMHKernel_offDiag_maximal_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:21:28.868801+00:00
-- url     : https://prove2.me/submissions/cd48bd49-ee92-4834-bdaa-4ec4dc00063c

import Mathlib
import Definitions.Def_TierneyMH_Shared_OffDiagDominates
import Definitions.Def_TierneyMH_Shared_mhKernel
import Definitions.Def_TierneyMH_Mixture_maxMHKernel
import Theorems.Thm_TierneyMH_Reversibility_theorem2_detailed_balance_iff
import Theorems.Thm_TierneyMH_Mixture_proposition1_canonical_split

open TierneyMH.Shared TierneyMH.Mixture

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem solution {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q]
    (α : E × E → ℝ≥0∞) (hα_meas : Measurable α) (hα_le : ∀ p, α p ≤ 1)
    (hrev : Kernel.IsReversible (mhKernel Q α) π) :
    OffDiagDominates π (maxMHKernel π Q) (mhKernel Q α) := by
  obtain ⟨hsplit, hratio⟩ := proposition1_canonical_split π Q
  obtain ⟨h0, h1⟩ := (TierneyMH.Reversibility.theorem2_detailed_balance_iff π Q α hα_meas hα_le
    (canonR π Q) (canonRatio π Q) hsplit hratio).1 hrev
  set R := canonR π Q with hRdef
  set r := canonRatio π Q with hrdef
  have hRm : MeasurableSet R := hsplit.1
  have hrm : Measurable r := hratio.1
  have hαMH_meas : Measurable (alphaMH π Q) := by
    unfold alphaMH
    exact Measurable.indicator (measurable_const.min (hrm.comp measurable_swap)) hRm
  -- α ≤ α_MH almost everywhere for μ = π ⊗ Q
  have hle : ∀ᵐ p ∂(π ⊗ₘ Q), α p ≤ alphaMH π Q p := by
    rw [← Measure.restrict_add_restrict_compl (μ := π ⊗ₘ Q) hRm, MeasureTheory.ae_add_measure_iff]
    constructor
    · filter_upwards [h1, ae_restrict_mem hRm] with p hp hpR
      rw [show alphaMH π Q p = min 1 (r p.swap) by
        simp only [alphaMH]; rw [Set.indicator_of_mem hpR]]
      refine le_min (hα_le p) ?_
      obtain ⟨hr0, hrtop⟩ := hratio.2.1 p
      rw [hratio.2.2.1 p]
      calc α p = α p * r p * (r p)⁻¹ := by
              rw [mul_assoc, ENNReal.mul_inv_cancel hr0.ne' hrtop.ne, mul_one]
        _ = α p.swap * (r p)⁻¹ := by rw [hp]
        _ ≤ 1 * (r p)⁻¹ := by gcongr; exact hα_le _
        _ = (r p)⁻¹ := one_mul _
    · filter_upwards [h0] with p hp
      rw [hp]; exact zero_le
  have hset : MeasurableSet {p : E × E | α p ≤ alphaMH π Q p} :=
    measurableSet_le hα_meas hαMH_meas
  rw [Measure.ae_compProd_iff hset] at hle
  filter_upwards [hle] with x hx A hA
  have hS : MeasurableSet (A \ {x}) := hA.diff (measurableSet_singleton x)
  have hxS : x ∉ A \ {x} := fun h => h.2 rfl
  have hunc_α : Measurable (Function.uncurry fun x y => α (x, y)) := hα_meas
  have hunc_MH : Measurable (Function.uncurry fun x y => alphaMH π Q (x, y)) := hαMH_meas
  simp only [maxMHKernel, mhKernel]
  simp only [Kernel.add_apply, Measure.add_apply]
  have hzero : (Kernel.withDensity Kernel.id (fun x _ => ∫⁻ u, (1 - α (x, u)) ∂(Q x))) x
      (A \ {x}) = 0 := by
    apply Kernel.withDensity_absolutelyContinuous
    simp [Kernel.id_apply, hxS]
  rw [hzero, add_zero, Kernel.withDensity_apply' Q hunc_α x _,
    Kernel.withDensity_apply' Q hunc_MH x _]
  refine le_trans ?_ le_self_add
  exact setLIntegral_mono_ae (hαMH_meas.comp measurable_prodMk_left).aemeasurable
    (hx.mono fun y hy _ => hy)
