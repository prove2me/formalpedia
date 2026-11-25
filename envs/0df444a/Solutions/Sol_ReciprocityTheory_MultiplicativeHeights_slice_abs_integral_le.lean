-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.slice_abs_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:50:21.285204+00:00
-- url     : https://prove2.me/submissions/29290a61-7aa9-4409-9513-0bbc8eadae29

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanD
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_coeffIn_eq_zero_of_lt
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrableOn_log_circ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integral_log_circ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_log_norm_leadingCoeff_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tmLog_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tmLog_update
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tmSlice_coeff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (f : MvPolynomial ι ℂ) (i : ι) (θ : ι → ℝ) :
    ∫ t, ‖tmLog f (update θ i t)‖ ∂unitIntervalMeasure ≤
      2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) +
        ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ| := by
  have hu : ∀ t, tmLog f (update θ i t) =
      Real.log ‖(tmSlice i (torusPoint θ) f).eval (circPt t)‖ := tmLog_update f θ i
  have hL : 0 ≤ posLog (∑ s ∈ f.support, ‖f.coeff s‖) := posLog_nonneg
  have hI : Integrable (fun t => tmLog f (update θ i t)) unitIntervalMeasure := by
    simp_rw [hu]; exact integrableOn_log_circ _
  have h1 : ∫ t, ‖tmLog f (update θ i t)‖ ∂unitIntervalMeasure ≤
      ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure := by
    refine integral_mono hI.norm ((integrable_const _).sub hI) fun t => ?_
    have := tmLog_le f (update θ i t)
    simp only [Real.norm_eq_abs]
    rcases abs_cases (tmLog f (update θ i t)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have h2 : ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure =
      2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) -
        (tmSlice i (torusPoint θ) f).logMahlerMeasure := by
    rw [integral_sub (integrable_const _) hI, integral_const]
    simp_rw [hu]
    rw [integral_log_circ]
    simp
  have h3 : |Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖| ≤
      ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ| := by
    rw [Polynomial.leadingCoeff, tmSlice_coeff]
    by_cases hn : (tmSlice i (torusPoint θ) f).natDegree < f.support.sup (fun s => s i) + 1
    · exact Finset.single_le_sum (f := fun k => |tmLog (coeffIn i k f) θ|)
        (fun k _ => abs_nonneg _) (Finset.mem_range.mpr hn)
    · rw [coeffIn_eq_zero_of_lt i f _ (by omega)]
      simp only [map_zero, norm_zero, Real.log_zero, abs_zero]
      exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have h4 := log_norm_leadingCoeff_le (tmSlice i (torusPoint θ) f)
  have h5 := neg_abs_le (Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖)
  linarith
end ReciprocityTheory.MultiplicativeHeights
