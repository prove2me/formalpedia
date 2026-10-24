-- Prove2me | solution 1 for UniversalBarrier.NSC.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:50:28.448703+00:00
-- url     : https://prove2.me/submissions/2bb32d1d-deac-4efe-b251-abe655349594

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

open MeasureTheory
namespace UniversalBarrier.NSC.MeanProof

lemma weighted_integrable (q : ℝ → ℝ) (hq0 : ∀ t, 0 ≤ q t)
    (hsupp : ∀ t ∉ Set.Icc (0 : ℝ) 1, q t=0) (hqi : Integrable q) :
    Integrable (fun t => t*q t) := by
  apply hqi.mono' (aestronglyMeasurable_id.mul hqi.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖t*q t‖ ≤ q t
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg ht.1 (hq0 t))]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (hq0 t)]
  · simp [hsupp t ht]

lemma reflection_bound (q : ℝ → ℝ) (hsupp : ∀ t ∉ Set.Icc (0 : ℝ) 1, q t=0)
    (hmono : AntitoneOn q (Set.Icc 0 1)) (t : ℝ) :
    t*q t+(1-t)*q (1-t) ≤ (1/2 : ℝ)*(q t+q (1-t)) := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · have hr : 1-t ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1,ht.2]
    by_cases hh : t ≤ 1/2
    · have hm := hmono ht hr (show t ≤ 1-t by linarith)
      have hp := mul_nonpos_of_nonpos_of_nonneg (show t-1/2 ≤ 0 by linarith)
        (show 0 ≤ q t-q (1-t) by linarith)
      nlinarith
    · have hm := hmono hr ht (show 1-t ≤ t by linarith)
      have hp := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ t-1/2 by linarith)
        (show q t-q (1-t) ≤ 0 by linarith)
      nlinarith
  · have hr : 1-t ∉ Set.Icc (0 : ℝ) 1 := by
      intro hh
      apply ht
      constructor <;> linarith [hh.1,hh.2]
    simp [hsupp t ht,hsupp (1-t) hr]

end UniversalBarrier.NSC.MeanProof

open UniversalBarrier.NSC UniversalBarrier.NSC.MeanProof

theorem solution (q : ℝ → ℝ) (hq0 : ∀ t, 0 ≤ q t) (hsupp : ∀ t ∉ Set.Icc (0 : ℝ) 1, q t = 0)
    (hmono : AntitoneOn q (Set.Icc 0 1)) (hq1 : ∫ t, q t = 1) :
    mu1 q ≤ 1 / 2 := by
  have hqi : Integrable q := Integrable.of_integral_ne_zero (by rw [hq1]; norm_num)
  have hti := weighted_integrable q hq0 hsupp hqi
  have hqr := hqi.comp_sub_left (1 : ℝ)
  have htr := hti.comp_sub_left (1 : ℝ)
  have hh := integral_mono (hti.add htr) ((hqi.add hqr).const_mul (1/2 : ℝ))
    (reflection_bound q hsupp hmono)
  change (∫ t, t*q t+(1-t)*q (1-t)) ≤ ∫ t, (1/2 : ℝ)*(q t+q (1-t)) at hh
  rw [integral_add hti htr,integral_const_mul,integral_add hqi hqr,
    integral_sub_left_eq_self q volume 1,
    integral_sub_left_eq_self (fun t => t*q t) volume 1,hq1] at hh
  unfold mu1
  linarith
