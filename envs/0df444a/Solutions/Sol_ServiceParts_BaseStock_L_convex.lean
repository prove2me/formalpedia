-- Prove2me | solution 1 for ServiceParts.BaseStock.L_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:47:04.871496+00:00
-- url     : https://prove2.me/submissions/bba6381c-9061-4a7b-9070-d47a5ea4f79c

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model

set_option autoImplicit false

open MeasureTheory Set

namespace ServiceParts.BaseStock.L_convex_aux

theorem max_comb (u v a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (a * u + b * v) 0 ≤ a * max u 0 + b * max v 0 := by
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left (le_max_left u 0) ha,
      mul_le_mul_of_nonneg_left (le_max_left v 0) hb]
  · have h1 : 0 ≤ max u 0 := le_max_right u 0
    have h2 : 0 ≤ max v 0 := le_max_right v 0
    positivity

theorem b_nonneg (M : Model) : 0 ≤ M.b := by
  have h0 : 0 ≤ (1 - M.α) / M.α * M.c := by
    apply mul_nonneg
    · apply div_nonneg
      · linarith [M.α_lt_one]
      · exact M.α_pos.le
    · exact M.c_nonneg
  linarith [M.b_gt]

theorem g_int (M : Model) : IntegrableOn M.g (Ioi 0) := by
  by_contra h
  have := integral_undef h
  rw [M.g_total] at this
  norm_num at this

theorem F_int (M : Model) (y : ℝ) :
    IntegrableOn (fun x => (M.h * max (y - x) 0 + M.b * max (x - y) 0) * M.g x) (Ioi 0) := by
  have hg := g_int M
  have hm := M.g_mean
  have hb := b_nonneg M
  have hh := M.h_pos.le
  refine Integrable.mono' ((hm.const_mul (M.h + M.b)).add (hg.const_mul ((M.h + M.b) * |y|))) ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    exact (by fun_prop : Continuous fun x : ℝ =>
      M.h * max (y - x) 0 + M.b * max (x - y) 0).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    have hgx : 0 < M.g x := M.g_pos x hx0
    have e1 : max (y - x) 0 ≤ x + |y| := max_le (by linarith [le_abs_self y]) (by positivity)
    have e2 : max (x - y) 0 ≤ x + |y| := max_le (by linarith [neg_abs_le y]) (by positivity)
    have n1 : 0 ≤ max (y - x) 0 := le_max_right _ _
    have n2 : 0 ≤ max (x - y) 0 := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (M.h * max (y - x) 0 + M.b * max (x - y) 0) ≤ (M.h + M.b) * (x + |y|) := by
      nlinarith [mul_le_mul_of_nonneg_left e1 hh, mul_le_mul_of_nonneg_left e2 hb]
    have := mul_le_mul_of_nonneg_right this hgx.le
    simp only [Pi.add_apply]
    nlinarith

theorem L_eq (M : Model) (y : ℝ) :
    M.L y = ∫ x in Ioi 0, (M.h * max (y - x) 0 + M.b * max (x - y) 0) * M.g x := by
  unfold Model.L
  split_ifs with hy
  · rw [← Ioc_union_Ioi_eq_Ioi hy.le,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((F_int M y).mono_set Ioc_subset_Ioi_self)
        ((F_int M y).mono_set (Ioi_subset_Ioi hy.le))]
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1
    · apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have h1 : max (y - x) 0 = y - x := max_eq_left (by linarith [hx.2])
      have h2 : max (x - y) 0 = 0 := max_eq_right (by linarith [hx.2])
      simp only [h1, h2]; ring
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx' : y < x := hx
      have h1 : max (y - x) 0 = 0 := max_eq_right (by linarith)
      have h2 : max (x - y) 0 = x - y := max_eq_left (by linarith)
      simp only [h1, h2]; ring
  · rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    have h1 : max (y - x) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (x - y) 0 = x - y := max_eq_left (by linarith)
    simp only [h1, h2]; ring

end ServiceParts.BaseStock.L_convex_aux

open ServiceParts.BaseStock MeasureTheory Set in
theorem solution (M : Model) : ConvexOn ℝ univ M.L := by
  refine ⟨convex_univ, ?_⟩
  intro y1 _ y2 _ a b ha hb hab
  simp only [smul_eq_mul]
  rw [L_convex_aux.L_eq, L_convex_aux.L_eq, L_convex_aux.L_eq, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((L_convex_aux.F_int M y1).const_mul a) ((L_convex_aux.F_int M y2).const_mul b)]
  apply setIntegral_mono_on (L_convex_aux.F_int M _) (((L_convex_aux.F_int M y1).const_mul a).add ((L_convex_aux.F_int M y2).const_mul b))
    measurableSet_Ioi
  intro x hx
  have hgx : 0 < M.g x := M.g_pos x hx
  have hbn := L_convex_aux.b_nonneg M
  have hh := M.h_pos.le
  have e1 : a * y1 + b * y2 - x = a * (y1 - x) + b * (y2 - x) := by
    linear_combination x * hab
  have e2 : x - (a * y1 + b * y2) = a * (x - y1) + b * (x - y2) := by
    linear_combination -(x * hab)
  rw [e1, e2]
  have m1 := L_convex_aux.max_comb (y1 - x) (y2 - x) a b ha hb
  have m2 := L_convex_aux.max_comb (x - y1) (x - y2) a b ha hb
  have key : M.h * max (a * (y1 - x) + b * (y2 - x)) 0 + M.b * max (a * (x - y1) + b * (x - y2)) 0
      ≤ a * (M.h * max (y1 - x) 0 + M.b * max (x - y1) 0)
        + b * (M.h * max (y2 - x) 0 + M.b * max (x - y2) 0) := by
    nlinarith [mul_le_mul_of_nonneg_left m1 hh, mul_le_mul_of_nonneg_left m2 hbn]
  have := mul_le_mul_of_nonneg_right key hgx.le
  simp only [Pi.add_apply]
  nlinarith
