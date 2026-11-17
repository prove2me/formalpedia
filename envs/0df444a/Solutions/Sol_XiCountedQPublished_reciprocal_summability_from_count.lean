-- Prove2me | solution 1 for XiCountedQPublished.reciprocal_summability_from_count
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:32:41.98919+00:00
-- url     : https://prove2.me/submissions/572f0512-c5d0-44e4-8773-3575e08cc144

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace ReciprocalCounting

theorem indicator_integrable (a : ℝ) :
    IntegrableOn ((Ioi a).indicator (fun y : ℝ => y^(-2 : ℝ))) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)).indicator measurableSet_Ioi

theorem indicator_integral (a : ℝ) (ha : 1 ≤ a) :
    (∫ y : ℝ in Ioi 1, (Ioi a).indicator (fun y : ℝ => y^(-2 : ℝ)) y) = a⁻¹ := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi ha)]
  have hh := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (show 0 < a by linarith)
  simpa only [show (-2 : ℝ)+1 = -1 by norm_num, Real.rpow_neg_one,
    div_neg, div_one, neg_neg] using hh

theorem summable_inverse_from_sublinear_count (a : ℕ → ℝ) (ha : ∀ j, 1 ≤ a j)
    (C r : ℝ) (hr : r < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ℕ,
      (∀ j ∈ F, a j ≤ y) → (F.card : ℝ) ≤ C*y^r) :
    Summable (fun j => (a j)⁻¹) ∧ (∑' j, (a j)⁻¹) ≤ C/(1-r) := by
  classical
  have hi : IntegrableOn (fun y : ℝ => C*y^(r-2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : r-2 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul C
  have hb (F : Finset ℕ) : (∑ j ∈ F, (a j)⁻¹) ≤ C/(1-r) := by
    calc
      _ = ∑ j ∈ F, ∫ y : ℝ in Ioi 1,
          (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (indicator_integral (a j) (ha j)).symm
      _ = ∫ y : ℝ in Ioi 1, ∑ j ∈ F,
          (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y :=
        (integral_finsetSum F (fun j _ => indicator_integrable (a j))).symm
      _ ≤ ∫ y : ℝ in Ioi 1, C*y^(r-2) := by
        apply integral_mono_ae (integrable_finset_sum F (fun j _ => indicator_integrable (a j))) hi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hy1 : 1 ≤ y := (mem_Ioi.mp hy).le
        have hy0 : 0 ≤ y := by linarith
        have he : (∑ j ∈ F, (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y) =
            ((F.filter (fun j => a j < y)).card : ℝ)*y^(-2 : ℝ) := by
          simp only [Set.indicator, mem_Ioi]
          rw [← Finset.sum_filter]
          simp
        rw [he]
        have hc := hcount y hy1 (F.filter (fun j => a j < y))
          (fun j hj => (Finset.mem_filter.mp hj).2.le)
        calc
          _ ≤ (C*y^r)*y^(-2 : ℝ) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hy0 _)
          _ = C*y^(r-2) := by rw [mul_assoc, ← Real.rpow_add (show 0 < y by linarith)]; congr 2 <;> ring
      _ = C/(1-r) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : r-2 < -1) (by norm_num)]
        rw [show r-2+1 = -(1-r) by ring]
        simp only [Real.one_rpow, div_neg, neg_neg, one_div]
        ring
  have hs := summable_of_sum_le (fun j => inv_nonneg.mpr (by linarith [ha j])) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

end ReciprocalCounting

theorem solution (a : ℕ → ℝ) (ha : ∀ j, 1 ≤ a j)
    (C r : ℝ) (hr : r < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ℕ,
      (∀ j ∈ F, a j ≤ y) → (F.card : ℝ) ≤ C*y^r) :
    Summable (fun j => (a j)⁻¹) ∧ (∑' j, (a j)⁻¹) ≤ C/(1-r) := by
  exact ReciprocalCounting.summable_inverse_from_sublinear_count a ha C r hr hcount
