-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P10.barycentricBallMass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:18:55.487153+00:00
-- url     : https://prove2.me/submissions/8ff0ecce-4aba-4807-b707-409af678b9e1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section HilbertResults

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [hcomplete : CompleteSpace H]

include hcomplete

lemma x8_main [SeparableSpace H]
    (delta : ℝ) (hdelta : 0 < delta) (z : H) (hz : ‖z‖ ≤ 1)
    (hnear : 1 - delta < ‖z‖)
    (mu : ProbabilityMeasure (Metric.closedBall (0 : H) 1))
    (hb : pettisBarycenter (Metric.closedBall (0 : H) 1) mu = z) :
    (delta ^ 2 - (1 - ‖z‖ ^ 2)) / (delta ^ 2 - (1 - ‖z‖) ^ 2) ≤
      ((mu : Measure (Metric.closedBall (0 : H) 1))
        {y | ‖(y : H) - z‖ ≤ delta}).toReal := by
  have hP' : z ≠ 0 → IsPettisBarycenter (Metric.closedBall (0 : H) 1) mu z := by
    intro hz0
    unfold pettisBarycenter at hb
    split_ifs at hb with h
    · rw [← hb]; exact Classical.choose_spec h
    · exact absurd hb.symm hz0
  clear hb
  set S : Set (Metric.closedBall (0 : H) 1) := {y | ‖(y : H) - z‖ ≤ delta}
  have hScl : IsClosed S :=
    isClosed_le (continuous_norm.comp (continuous_subtype_val.sub continuous_const)) continuous_const
  have hS : MeasurableSet S := hScl.measurableSet
  have hyA : ∀ y : (Metric.closedBall (0 : H) 1), ‖(y : H)‖ ≤ 1 := by
    intro y; exact mem_closedBall_zero_iff.1 y.2
  set r := ‖z‖
  have hden : 0 < delta ^ 2 - (1 - r) ^ 2 := by
    have h1 : 0 ≤ 1 - r := by linarith
    nlinarith
  by_cases hz0 : z = 0
  · have hr : r = 0 := by simp [r, hz0]
    have hSu : S = univ := by
      ext y; simp only [S, mem_setOf_eq, mem_univ, iff_true, hz0, sub_zero]
      have := hyA y; rw [hr] at hnear; linarith
    rw [hSu, measure_univ, ENNReal.toReal_one, hr]
    rw [hr] at hden
    rw [div_le_one hden]; norm_num
  have hrpos : 0 < r := norm_pos_iff.2 hz0
  have hP : IsPettisBarycenter (Metric.closedBall (0 : H) 1) mu z := hP' hz0
  set u : H := (1 / r) • z
  set l : H →L[ℝ] ℝ := innerSL ℝ u
  have hl : ∀ x : H, l x = inner ℝ x z / r := by
    intro x
    simp only [l, u, innerSL_apply_apply, inner_smul_left]
    rw [real_inner_comm]; simp [div_eq_inv_mul]
  obtain ⟨hint, hlz⟩ := hP l
  have hlz' : l z = r := by
    rw [hl, real_inner_self_eq_norm_sq, pow_two, mul_div_assoc, div_self hrpos.ne', mul_one]
  set c : ℝ := (1 + r ^ 2 - delta ^ 2) / (2 * r)
  have h2rc : 2 * r * c = 1 + r ^ 2 - delta ^ 2 := by
    simp only [c]; field_simp
  -- pointwise bound
  set g : (Metric.closedBall (0 : H) 1) → ℝ := fun y => c + S.indicator (fun _ => 1 - c) y
  have hle : ∀ y : (Metric.closedBall (0 : H) 1), l (y : H) ≤ g y := by
    intro y
    simp only [g]
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy]
      have : l (y : H) ≤ 1 := by
        have h1 := real_inner_le_norm (y : H) u
        have hu : ‖u‖ = 1 := by
          simp only [u]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 hrpos), one_div,
            inv_mul_cancel₀ hrpos.ne']
        calc l (y : H) = inner ℝ u (y : H) := by simp [l]
          _ ≤ ‖u‖ * ‖(y : H)‖ := real_inner_le_norm _ _
          _ ≤ 1 := by rw [hu, one_mul]; exact hyA y
      linarith
    · rw [indicator_of_notMem hy, add_zero, hl, div_le_iff₀ hrpos]
      have hy' : delta < ‖(y : H) - z‖ := by simpa [S] using hy
      have e := norm_sub_sq_real (y : H) z
      have := hyA y
      have hd2 : delta ^ 2 < ‖(y : H) - z‖ ^ 2 := by nlinarith
      have hy2 : ‖(y : H)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (y : H)]
      nlinarith
  have hgint : Integrable g (mu : Measure (Metric.closedBall (0 : H) 1)) :=
    (integrable_const c).add ((integrable_const (1 - c)).indicator hS)
  have hmono := integral_mono hint hgint hle
  have hgval : ∫ y, g y ∂(mu : Measure (Metric.closedBall (0 : H) 1)) = c + ((mu : Measure (Metric.closedBall (0 : H) 1)) S).toReal * (1 - c) := by
    simp only [g]
    rw [integral_add (integrable_const c) ((integrable_const (1 - c)).indicator hS),
      integral_const, integral_indicator_const _ hS]
    simp [Measure.real]
  rw [← hlz, hlz', hgval] at hmono
  set m := ((mu : Measure (Metric.closedBall (0 : H) 1)) S).toReal
  rw [div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_left hmono (by linarith : (0 : ℝ) ≤ 2 * r)]

end HilbertResults

end QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Frontier18.P10 in
open QAlgorithms.Papers.Independent.Dependency50.P25 in
attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable in
attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel in
theorem solution {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [hcomplete : CompleteSpace H] [SeparableSpace H]
    (delta : ℝ) (hdelta : 0 < delta) (z : H) (hz : ‖z‖ ≤ 1)
    (hnear : 1 - delta < ‖z‖)
    (mu : ProbabilityMeasure (Metric.closedBall (0 : H) 1))
    (hb : pettisBarycenter (Metric.closedBall (0 : H) 1) mu = z) :
    (delta ^ 2 - (1 - ‖z‖ ^ 2)) / (delta ^ 2 - (1 - ‖z‖) ^ 2) ≤
      ((mu : Measure (Metric.closedBall (0 : H) 1))
        {y | ‖(y : H) - z‖ ≤ delta}).toReal :=
  x8_main delta hdelta z hz hnear mu hb
