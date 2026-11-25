-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_eLpNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:40.618699+00:00
-- url     : https://prove2.me/submissions/765629c5-ae57-49ff-9720-a5c4d76857d5

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_sq_lintegral_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS
private lemma eLpNorm_two_rpow_two_eq_lintegral {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} (f : Y → ℂ) :
    eLpNorm f 2 ν ^ (2:ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), ← ENNReal.rpow_mul]
  norm_num
section Mat
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {k : WithTop ℕ∞}
end Mat
section Ret
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
end Ret
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (r : X → ℂ) (D : ℝ → X → ℂ) (hD : Measurable (Function.uncurry D))
    (hr : ∀ x, r x = ∫ s in (0:ℝ)..1, D s x) (B : ENNReal)
    (hB : ∀ s ∈ Ioc (0:ℝ) 1, eLpNorm (D s) 2 μ ≤ B) : eLpNorm r 2 μ ≤ B := by
  have hmeas : ∀ x, Measurable fun s => D s x := fun x => hD.of_uncurry_right
  have hpt : ∀ x, ‖r x‖ₑ ≤ ∫⁻ s in Ioc (0:ℝ) 1, ‖D s x‖ₑ := fun x => by
    rw [hr x, intervalIntegral.integral_of_le zero_le_one]
    exact enorm_integral_le_lintegral_enorm _
  have hsq : ∀ s ∈ Ioc (0:ℝ) 1, ∫⁻ x, ‖D s x‖ₑ ^ (2:ℝ) ∂μ ≤ B ^ (2:ℝ) := fun s hs => by
    rw [← eLpNorm_two_rpow_two_eq_lintegral]
    exact ENNReal.rpow_le_rpow (hB s hs) (by norm_num)
  have hmain : eLpNorm r 2 μ ^ (2:ℝ) ≤ B ^ (2:ℝ) := by
    rw [eLpNorm_two_rpow_two_eq_lintegral]
    calc ∫⁻ x, ‖r x‖ₑ ^ (2:ℝ) ∂μ
        ≤ ∫⁻ x, (∫⁻ s in Ioc (0:ℝ) 1, ‖D s x‖ₑ) ^ (2:ℝ) ∂μ :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) (by norm_num)
      _ ≤ ∫⁻ x, (∫⁻ s in Ioc (0:ℝ) 1, ‖D s x‖ₑ ^ (2:ℝ)) ∂μ :=
          lintegral_mono fun x => slm_sq_lintegral_le (hmeas x).enorm.aemeasurable
      _ = ∫⁻ s in Ioc (0:ℝ) 1, ∫⁻ x, ‖D s x‖ₑ ^ (2:ℝ) ∂μ :=
          lintegral_lintegral_swap (((hD.comp measurable_swap).enorm.pow_const (2:ℝ)).aemeasurable)
      _ ≤ ∫⁻ s in Ioc (0:ℝ) 1, B ^ (2:ℝ) := setLIntegral_mono' measurableSet_Ioc hsq
      _ = B ^ (2:ℝ) := by simp [Real.volume_Ioc]
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < 2)).mp hmain
end ReciprocityTheory.ChartRestriction.DS
