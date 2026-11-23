-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integrableOn_radK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:27.438223+00:00
-- url     : https://prove2.me/submissions/2afb0ab8-506d-4581-bd60-1c7264df3bfa

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrableOn_radJ

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
open MeasureTheory Set Real Filter Topology
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) :
    IntegrableOn (fun r : ℝ => r ^ k * log r * exp (-r ^ 2)) (Ioi 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ((integrableOn_radJ (m + 2)).add (integrableOn_radJ m)).mono' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r (hr : 0 < r) => ?_)
    have hlog : |log r| ≤ r + r⁻¹ := by
      rcases le_or_gt 0 (log r) with h | h
      · rw [abs_of_nonneg h]
        have := Real.log_le_sub_one_of_pos hr
        have : 0 < r⁻¹ := inv_pos.2 hr
        linarith
      · rw [abs_of_neg h, ← Real.log_inv]
        have := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
        linarith
    have he := exp_pos (-r ^ 2)
    have hpow : r ^ (m + 1) * (r + r⁻¹) = r ^ (m + 2) + r ^ m := by
      field_simp
      ring
    have hmain : r ^ (m + 1) * |log r| ≤ r ^ (m + 2) + r ^ m := by
      rw [← hpow]
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_pos he, abs_of_pos (pow_pos hr _)]
    calc r ^ (m + 1) * |log r| * exp (-r ^ 2) ≤ (r ^ (m + 2) + r ^ m) * exp (-r ^ 2) :=
          mul_le_mul_of_nonneg_right hmain he.le
      _ = r ^ (m + 2) * exp (-r ^ 2) + r ^ m * exp (-r ^ 2) := by ring
end ReciprocityTheory.MultiplicativeHeights
