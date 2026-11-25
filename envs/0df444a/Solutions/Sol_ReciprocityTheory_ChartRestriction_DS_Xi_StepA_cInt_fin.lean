-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.cInt_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:50.749804+00:00
-- url     : https://prove2.me/submissions/417f3d6b-0ee6-47ef-a9d3-e6c6fa7fbceb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ScaleInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergMapContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_EIntBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (n : ℕ) (σ : ℝ) (h1 : 1 < σ) (h2 : σ < 2 * (n : ℝ) + 1) :
    (∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ)) *
      ENNReal.ofReal (min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹)) < ∞ := by
  have hF0 : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioc 0 1) := by
    refine Integrable.mono'
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := 2 * (n : ℝ) - σ)
        (by linarith)).1 ?_ ?_
    · first
        | exact (by measurability : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
        | exact (by fun_prop : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun y hy => ?_)
      have hy0 : 0 < y := hy.1
      have hA : 0 ≤ y ^ (2 * (n : ℝ) - σ) := Real.rpow_nonneg hy0.le _
      have hmin : 0 ≤ min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹ := le_min (Real.rpow_nonneg hy0.le _) (inv_nonneg.2 hy0.le)
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (mul_nonneg hA hmin))]
      calc y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹) ≤ y * (y ^ (2 * (n : ℝ) - σ) * y⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _) hA) hy0.le
        _ = y ^ (2 * (n : ℝ) - σ) := by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hy0.ne', mul_one]
  have hF1 : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioi 1) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -σ) (by linarith) zero_lt_one) ?_ ?_
    · first
        | exact (by measurability : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
        | exact (by fun_prop : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y hy => ?_)
      have hy0 : 0 < y := zero_lt_one.trans hy
      have hA : 0 ≤ y ^ (2 * (n : ℝ) - σ) := Real.rpow_nonneg hy0.le _
      have hmin : 0 ≤ min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹ := le_min (Real.rpow_nonneg hy0.le _) (inv_nonneg.2 hy0.le)
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (mul_nonneg hA hmin))]
      calc y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹) ≤ y * (y ^ (2 * (n : ℝ) - σ) * y ^ (-((2 * n + 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_left _ _) hA) hy0.le
        _ = y ^ (-σ) := by
          rw [← mul_assoc, mul_comm y, ← Real.rpow_add_one hy0.ne', ← Real.rpow_add hy0]
          congr 1
          push_cast
          ring
  have hY : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hF0.union hF1
  have hI : Integrable (fun c : ℂ => ‖c‖ ^ (2 * (n : ℝ) - σ) *
      min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹) volume := by
    first
      | exact (integrable_fun_norm_addHaar volume
          (f := fun y : ℝ => (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹))).2 (hY.congr_fun (fun y _ => by simp) measurableSet_Ioi)
      | exact (integrable_fun_norm_addHaar (μ := volume)
          (f := fun y : ℝ => (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹))).2 (hY.congr_fun (fun y _ => by simp) measurableSet_Ioi)
  calc (∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ)) *
        ENNReal.ofReal (min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹))
      = ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ) *
          min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹) :=
        lintegral_congr fun c => (ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)).symm
    _ < ∞ := hI.lintegral_lt_top
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
