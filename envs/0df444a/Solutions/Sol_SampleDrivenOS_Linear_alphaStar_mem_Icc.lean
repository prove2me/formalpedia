-- Prove2me | solution 1 for SampleDrivenOS.Linear.alphaStar_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:12:54.542536+00:00
-- url     : https://prove2.me/submissions/9fc85209-90b3-4dce-9a9e-72801e51ef7a

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

set_option autoImplicit false
open SampleDrivenOS.Linear

/-- the series part `S_n(x) = ∑_{i<n} x^{i+1}/(i+1)`. -/
noncomputable def asS (n : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)

lemma as_neglog_r (r : ℝ) (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 1) (n : ℕ) :
    asS n (1 - r) - (1 - r) ^ (n + 1) / r ≤ -Real.log r ∧
      -Real.log r ≤ asS n (1 - r) + (1 - r) ^ (n + 1) / r := by
  have hx0 : 0 ≤ 1 - r := by linarith
  have hx : |1 - r| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg hx0, show 1 - (1 - r) = r by ring] at h
  rw [abs_le] at h
  unfold asS
  constructor <;> linarith [h.1, h.2]

lemma as_neglog_lower (y r : ℝ) (j n : ℕ) (hy : y = r / 2 ^ j) (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 1) :
    (j : ℝ) * 0.6931471803 + asS n (1 - r) - (1 - r) ^ (n + 1) / r ≤ -Real.log y := by
  have hr0 : 0 < r := by linarith
  have h1 := (as_neglog_r r hr1 hr2 n).1
  have h2 := Real.log_two_gt_d9
  rw [hy, Real.log_div hr0.ne' (by positivity), Real.log_pow]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

lemma as_neglog_upper (y r : ℝ) (j n : ℕ) (hy : y = r / 2 ^ j) (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 1) :
    -Real.log y ≤ (j : ℝ) * 0.6931471808 + asS n (1 - r) + (1 - r) ^ (n + 1) / r := by
  have hr0 : 0 < r := by linarith
  have h1 := (as_neglog_r r hr1 hr2 n).2
  have h2 := Real.log_two_lt_d9
  rw [hy, Real.log_div hr0.ne' (by positivity), Real.log_pow]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-- `φ(y) = y (1 - log y)` -/
lemma as_phi_cont : Continuous fun y : ℝ => y * (1 - Real.log y) := by
  have : (fun y : ℝ => y * (1 - Real.log y)) = fun y => y - y * Real.log y := by
    funext y; ring
  rw [this]
  exact continuous_id.sub Real.continuous_mul_log

lemma as_phi_nonneg (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ y * (1 - Real.log y) := by
  have : Real.log y ≤ 0 := Real.log_nonpos hy0 hy1
  have : 0 ≤ 1 - Real.log y := by linarith
  positivity

lemma as_phi_concave : ConcaveOn ℝ (Set.Ici 0) (fun y : ℝ => y * (1 - Real.log y)) := by
  have h1 : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun y : ℝ => -(y * Real.log y)) :=
    Real.convexOn_mul_log.neg
  have h2 : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun y : ℝ => y) := concaveOn_id (convex_Ici 0)
  have := h2.add h1
  refine this.congr ?_
  intro y _
  simp only [Pi.add_apply]
  ring

/-- tangent-line bound `φ(y) ≤ y₀ - y log y₀`. -/
lemma as_phi_tangent (y y0 : ℝ) (hy : 0 ≤ y) (hy0 : 0 < y0) :
    y * (1 - Real.log y) ≤ y0 - y * Real.log y0 := by
  rcases hy.eq_or_lt with h | h
  · subst h; simp; linarith
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < y0 / y by positivity)
    rw [Real.log_div hy0.ne' h.ne'] at h1
    have h2 : y0 / y * y = y0 := by field_simp
    nlinarith

lemma as_int_affine (α β u v : ℝ) :
    ∫ y in u..v, (α + β * y) = α * (v - u) + β * (v ^ 2 - u ^ 2) / 2 := by
  have hd : ∀ x ∈ Set.uIcc u v, HasDerivAt (fun y : ℝ => α * y + β * (y ^ 2 / 2)) (α + β * x) x := by
    intro x _
    have := ((hasDerivAt_id x).const_mul α).add (((hasDerivAt_pow 2 x).div_const 2).const_mul β)
    refine this.congr_deriv ?_
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  ring

lemma as_cont_on (c u v : ℝ) (hc : 0 < c) (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1) :
    IntervalIntegrable (fun y => 1 / (y * (1 - Real.log y) + c)) MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huv]
  apply continuousOn_const.div ((as_phi_cont.add continuous_const).continuousOn)
  intro y hy
  have := as_phi_nonneg y (le_trans hu0 hy.1) (le_trans hy.2 hv1)
  simp only [Pi.add_apply]
  linarith

/-- trapezoid upper bound on `[u, v]`. -/
lemma as_trap_upper (c u v Lu Lv : ℝ) (hc : 0 < c) (hu0 : 0 ≤ u) (huv : u < v) (hv1 : v ≤ 1)
    (hLu0 : 0 ≤ Lu) (hLv0 : 0 ≤ Lv)
    (hLu : Lu ≤ u * (1 - Real.log u)) (hLv : Lv ≤ v * (1 - Real.log v)) :
    ∫ y in u..v, 1 / (y * (1 - Real.log y) + c) ≤ (v - u) / 2 * (1 / (c + Lu) + 1 / (c + Lv)) := by
  set A := c + Lu with hA
  set B := c + Lv with hB
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hvu : 0 < v - u := by linarith
  set α : ℝ := 1 / B + v * (1 / A - 1 / B) / (v - u) with hα
  set β : ℝ := -((1 / A - 1 / B) / (v - u)) with hβ
  have hpt : ∀ y ∈ Set.Icc u v, 1 / (y * (1 - Real.log y) + c) ≤ α + β * y := by
    intro y hy
    set θ := (v - y) / (v - u) with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hy.2]) hvu.le
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hvu]; linarith [hy.1]
    have hyθ : θ * u + (1 - θ) * v = y := by rw [hθ]; field_simp; ring
    have hconc := as_phi_concave.2 (show u ∈ Set.Ici (0 : ℝ) from hu0)
      (show v ∈ Set.Ici (0 : ℝ) from le_trans hu0 huv.le) hθ0 (by linarith : 0 ≤ 1 - θ)
      (by ring : θ + (1 - θ) = 1)
    simp only [smul_eq_mul] at hconc
    rw [hyθ] at hconc
    have hlam : θ * Lu + (1 - θ) * Lv ≤ y * (1 - Real.log y) := by
      have h1 : θ * Lu ≤ θ * (u * (1 - Real.log u)) := mul_le_mul_of_nonneg_left hLu hθ0
      have h2 : (1 - θ) * Lv ≤ (1 - θ) * (v * (1 - Real.log v)) :=
        mul_le_mul_of_nonneg_left hLv (by linarith)
      linarith
    have hX : θ * A + (1 - θ) * B ≤ y * (1 - Real.log y) + c := by
      rw [hA, hB]; nlinarith
    have hXpos : 0 < θ * A + (1 - θ) * B := by nlinarith
    have hrhs : α + β * y = θ / A + (1 - θ) / B := by
      rw [hα, hβ, hθ]; field_simp; ring
    rw [hrhs]
    calc 1 / (y * (1 - Real.log y) + c) ≤ 1 / (θ * A + (1 - θ) * B) :=
          one_div_le_one_div_of_le hXpos hX
      _ ≤ θ / A + (1 - θ) / B := by
          rw [div_add_div _ _ hA0.ne' hB0.ne', div_le_div_iff₀ hXpos (by positivity)]
          nlinarith [sq_nonneg (A - B), mul_nonneg hθ0 (by linarith : 0 ≤ 1 - θ)]
  have hmono := intervalIntegral.integral_mono_on huv.le (as_cont_on c u v hc hu0 huv.le hv1)
    ((continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable
      (u := fun y => α + β * y) _ _) hpt
  rw [as_int_affine] at hmono
  refine le_trans hmono (le_of_eq ?_)
  rw [hα, hβ]
  field_simp
  ring

/-- midpoint (tangent-line) lower bound on `[u, v]`. -/
lemma as_mid_lower (c u v y0 U : ℝ) (hc : 0 < c) (hu0 : 0 ≤ u) (huv : u < v) (hv1 : v ≤ 1)
    (hy0 : 0 < y0) (hU : -Real.log y0 ≤ U) (hU0 : 0 ≤ U) :
    (v - u) / (c + y0 + U * ((u + v) / 2)) ≤ ∫ y in u..v, 1 / (y * (1 - Real.log y) + c) := by
  set D := c + y0 + U * ((u + v) / 2) with hD
  have hD0 : 0 < D := by
    have : 0 ≤ U * ((u + v) / 2) := mul_nonneg hU0 (by linarith)
    linarith
  set α : ℝ := 2 / D - (c + y0) / D ^ 2 with hα
  set β : ℝ := -(U / D ^ 2) with hβ
  have hpt : ∀ y ∈ Set.Icc u v, α + β * y ≤ 1 / (y * (1 - Real.log y) + c) := by
    intro y hy
    have hy0' : 0 ≤ y := le_trans hu0 hy.1
    have htan := as_phi_tangent y y0 hy0' hy0
    have hφ : y * (1 - Real.log y) ≤ y0 + U * y := by nlinarith
    have hφ0 := as_phi_nonneg y hy0' (le_trans hy.2 hv1)
    set X := y * (1 - Real.log y) + c with hX
    have hX0 : 0 < X := by linarith
    have hXle : X ≤ c + y0 + U * y := by rw [hX]; linarith
    have hlin : α + β * y = 2 / D - (c + y0 + U * y) / D ^ 2 := by
      rw [hα, hβ]; ring
    rw [hlin]
    have h1 : 2 / D - X / D ^ 2 ≤ 1 / X := by
      rw [div_sub_div _ _ hD0.ne' (by positivity), div_le_div_iff₀ (by positivity) hX0]
      nlinarith [sq_nonneg (X - D), hD0, hX0]
    have h2 : 2 / D - (c + y0 + U * y) / D ^ 2 ≤ 2 / D - X / D ^ 2 := by
      have : X / D ^ 2 ≤ (c + y0 + U * y) / D ^ 2 :=
        div_le_div_of_nonneg_right hXle (by positivity)
      linarith
    linarith
  have hmono := intervalIntegral.integral_mono_on huv.le
    ((continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable
      (u := fun y => α + β * y) _ _)
    (as_cont_on c u v hc hu0 huv.le hv1) hpt
  rw [as_int_affine] at hmono
  refine le_trans (le_of_eq ?_) hmono
  rw [hα, hβ]
  field_simp
  ring

lemma as_L0 : (0 : ℝ) ≤ (0 : ℝ) * (1 - Real.log (0 : ℝ)) := by simp

lemma as_L1 : (56037/1000000 : ℝ) ≤ (1/100 : ℝ) * (1 - Real.log (1/100 : ℝ)) := by
  have h := as_neglog_lower (1/100 : ℝ) (16/25 : ℝ) 6 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : (4603781/1000000 : ℝ) ≤ ((6 : ℕ) : ℝ) * 0.6931471803 + asS 6 (1 - (16/25 : ℝ)) - (1 - (16/25 : ℝ)) ^ (6 + 1) / (16/25 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  nlinarith

lemma as_L2 : (168699/1000000 : ℝ) ≤ (1/25 : ℝ) * (1 - Real.log (1/25 : ℝ)) := by
  have h := as_neglog_lower (1/25 : ℝ) (16/25 : ℝ) 4 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : (3217487/1000000 : ℝ) ≤ ((4 : ℕ) : ℝ) * 0.6931471803 + asS 6 (1 - (16/25 : ℝ)) - (1 - (16/25 : ℝ)) ^ (6 + 1) / (16/25 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  nlinarith

lemma as_L3 : (61339/200000 : ℝ) ≤ (9/100 : ℝ) * (1 - Real.log (9/100 : ℝ)) := by
  have h := as_neglog_lower (9/100 : ℝ) (18/25 : ℝ) 3 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : (601933/250000 : ℝ) ≤ ((3 : ℕ) : ℝ) * 0.6931471803 + asS 6 (1 - (18/25 : ℝ)) - (1 - (18/25 : ℝ)) ^ (6 + 1) / (18/25 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  nlinarith

lemma as_L4 : (45299/100000 : ℝ) ≤ (4/25 : ℝ) * (1 - Real.log (4/25 : ℝ)) := by
  have h := as_neglog_lower (4/25 : ℝ) (16/25 : ℝ) 2 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : (1831193/1000000 : ℝ) ≤ ((2 : ℕ) : ℝ) * 0.6931471803 + asS 6 (1 - (16/25 : ℝ)) - (1 - (16/25 : ℝ)) ^ (6 + 1) / (16/25 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  nlinarith

lemma as_L5 : (592167/1000000 : ℝ) ≤ (1/4 : ℝ) * (1 - Real.log (1/4 : ℝ)) := by
  have h := as_neglog_lower (1/4 : ℝ) (1/2 : ℝ) 1 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : (342167/250000 : ℝ) ≤ ((1 : ℕ) : ℝ) * 0.6931471803 + asS 6 (1 - (1/2 : ℝ)) - (1 - (1/2 : ℝ)) ^ (6 + 1) / (1/2 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  nlinarith

lemma as_L6 : (727717/1000000 : ℝ) ≤ (9/25 : ℝ) * (1 - Real.log (9/25 : ℝ)) := by
  have h := as_neglog_lower (9/25 : ℝ) (18/25 : ℝ) 1 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : (510719/500000 : ℝ) ≤ ((1 : ℕ) : ℝ) * 0.6931471803 + asS 6 (1 - (18/25 : ℝ)) - (1 - (18/25 : ℝ)) ^ (6 + 1) / (18/25 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  nlinarith

lemma as_L7 : (839541/1000000 : ℝ) ≤ (49/100 : ℝ) * (1 - Real.log (49/100 : ℝ)) := by
  have h := as_neglog_lower (49/100 : ℝ) (49/50 : ℝ) 1 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : (713349/1000000 : ℝ) ≤ ((1 : ℕ) : ℝ) * 0.6931471803 + asS 6 (1 - (49/50 : ℝ)) - (1 - (49/50 : ℝ)) ^ (6 + 1) / (49/50 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  nlinarith

lemma as_L8 : (462367/500000 : ℝ) ≤ (16/25 : ℝ) * (1 - Real.log (16/25 : ℝ)) := by
  have h := as_neglog_lower (16/25 : ℝ) (16/25 : ℝ) 0 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : (222449/500000 : ℝ) ≤ ((0 : ℕ) : ℝ) * 0.6931471803 + asS 6 (1 - (16/25 : ℝ)) - (1 - (16/25 : ℝ)) ^ (6 + 1) / (16/25 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  nlinarith

lemma as_L9 : (980673/1000000 : ℝ) ≤ (81/100 : ℝ) * (1 - Real.log (81/100 : ℝ)) := by
  have h := as_neglog_lower (81/100 : ℝ) (81/100 : ℝ) 0 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : (52677/250000 : ℝ) ≤ ((0 : ℕ) : ℝ) * 0.6931471803 + asS 6 (1 - (81/100 : ℝ)) - (1 - (81/100 : ℝ)) ^ (6 + 1) / (81/100 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  nlinarith

lemma as_L10 : (1 : ℝ) ≤ (1 : ℝ) * (1 - Real.log (1 : ℝ)) := by
  have h := as_neglog_lower (1 : ℝ) (1 : ℝ) 0 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) * 0.6931471803 + asS 6 (1 - (1 : ℝ)) - (1 - (1 : ℝ)) ^ (6 + 1) / (1 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  nlinarith

lemma as_U0 : -Real.log (1/200 : ℝ) ≤ (2649689/500000 : ℝ) := by
  have h := as_neglog_upper (1/200 : ℝ) (16/25 : ℝ) 7 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : ((7 : ℕ) : ℝ) * 0.6931471808 + asS 6 (1 - (16/25 : ℝ)) + (1 - (16/25 : ℝ)) ^ (6 + 1) / (16/25 : ℝ) ≤ (2649689/500000 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  linarith

lemma as_U1 : -Real.log (1/40 : ℝ) ≤ (1844447/500000 : ℝ) := by
  have h := as_neglog_upper (1/40 : ℝ) (4/5 : ℝ) 5 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : ((5 : ℕ) : ℝ) * 0.6931471808 + asS 6 (1 - (4/5 : ℝ)) + (1 - (4/5 : ℝ)) ^ (6 + 1) / (4/5 : ℝ) ≤ (1844447/500000 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  linarith

lemma as_U2 : -Real.log (13/200 : ℝ) ≤ (2743201/1000000 : ℝ) := by
  have h := as_neglog_upper (13/200 : ℝ) (13/25 : ℝ) 3 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : ((3 : ℕ) : ℝ) * 0.6931471808 + asS 6 (1 - (13/25 : ℝ)) + (1 - (13/25 : ℝ)) ^ (6 + 1) / (13/25 : ℝ) ≤ (2743201/1000000 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  linarith

lemma as_U3 : -Real.log (1/8 : ℝ) ≤ (1046533/500000 : ℝ) := by
  have h := as_neglog_upper (1/8 : ℝ) (1/2 : ℝ) 2 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : ((2 : ℕ) : ℝ) * 0.6931471808 + asS 6 (1 - (1/2 : ℝ)) + (1 - (1/2 : ℝ)) ^ (6 + 1) / (1/2 : ℝ) ≤ (1046533/500000 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  linarith

lemma as_U4 : -Real.log (41/200 : ℝ) ≤ (99047/62500 : ℝ) := by
  have h := as_neglog_upper (41/200 : ℝ) (41/50 : ℝ) 2 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : ((2 : ℕ) : ℝ) * 0.6931471808 + asS 6 (1 - (41/50 : ℝ)) + (1 - (41/50 : ℝ)) ^ (6 + 1) / (41/50 : ℝ) ≤ (99047/62500 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  linarith

lemma as_U5 : -Real.log (61/200 : ℝ) ≤ (237879/200000 : ℝ) := by
  have h := as_neglog_upper (61/200 : ℝ) (61/100 : ℝ) 1 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : ((1 : ℕ) : ℝ) * 0.6931471808 + asS 6 (1 - (61/100 : ℝ)) + (1 - (61/100 : ℝ)) ^ (6 + 1) / (61/100 : ℝ) ≤ (237879/200000 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  linarith

lemma as_U6 : -Real.log (17/40 : ℝ) ≤ (213917/250000 : ℝ) := by
  have h := as_neglog_upper (17/40 : ℝ) (17/20 : ℝ) 1 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : ((1 : ℕ) : ℝ) * 0.6931471808 + asS 6 (1 - (17/20 : ℝ)) + (1 - (17/20 : ℝ)) ^ (6 + 1) / (17/20 : ℝ) ≤ (213917/250000 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  linarith

lemma as_U7 : -Real.log (113/200 : ℝ) ≤ (575463/1000000 : ℝ) := by
  have h := as_neglog_upper (113/200 : ℝ) (113/200 : ℝ) 0 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : ((0 : ℕ) : ℝ) * 0.6931471808 + asS 6 (1 - (113/200 : ℝ)) + (1 - (113/200 : ℝ)) ^ (6 + 1) / (113/200 : ℝ) ≤ (575463/1000000 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  linarith

lemma as_U8 : -Real.log (29/40 : ℝ) ≤ (160863/500000 : ℝ) := by
  have h := as_neglog_upper (29/40 : ℝ) (29/40 : ℝ) 0 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : ((0 : ℕ) : ℝ) * 0.6931471808 + asS 6 (1 - (29/40 : ℝ)) + (1 - (29/40 : ℝ)) ^ (6 + 1) / (29/40 : ℝ) ≤ (160863/500000 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  linarith

lemma as_U9 : -Real.log (181/200 : ℝ) ≤ (99821/1000000 : ℝ) := by
  have h := as_neglog_upper (181/200 : ℝ) (181/200 : ℝ) 0 6 (by norm_num) (by norm_num) (by norm_num)
  have hn : ((0 : ℕ) : ℝ) * 0.6931471808 + asS 6 (1 - (181/200 : ℝ)) + (1 - (181/200 : ℝ)) ^ (6 + 1) / (181/200 : ℝ) ≤ (99821/1000000 : ℝ) := by
    norm_num [asS, Finset.sum_range_succ]
  linarith

lemma as_up0 : ∫ y in (0 : ℝ)..(1/100 : ℝ), 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) ≤ (265041/10000000 : ℝ) := by
  have h := as_trap_upper (13/37 : ℝ) (0 : ℝ) (1/100 : ℝ) (0 : ℝ) (56037/1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_L0 as_L1
  have hb : ((1/100 : ℝ) - (0 : ℝ)) / 2 * (1 / ((13/37 : ℝ) + (0 : ℝ)) + 1 / ((13/37 : ℝ) + (56037/1000000 : ℝ))) ≤ (265041/10000000 : ℝ) := by norm_num
  linarith

lemma as_lo0 : (2741/100000 : ℝ) ≤ ∫ y in (0 : ℝ)..(1/100 : ℝ), 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) := by
  have h := as_mid_lower (1/3 : ℝ) (0 : ℝ) (1/100 : ℝ) (1/200 : ℝ) (2649689/500000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_U0 (by norm_num)
  have hb : (2741/100000 : ℝ) ≤ ((1/100 : ℝ) - (0 : ℝ)) / ((1/3 : ℝ) + (1/200 : ℝ) + (2649689/500000 : ℝ) * (((0 : ℝ) + (1/100 : ℝ)) / 2)) := by norm_num
  linarith

lemma as_up1 : ∫ y in (1/100 : ℝ)..(1/25 : ℝ), 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) ≤ (656633/10000000 : ℝ) := by
  have h := as_trap_upper (13/37 : ℝ) (1/100 : ℝ) (1/25 : ℝ) (56037/1000000 : ℝ) (168699/1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_L1 as_L2
  have hb : ((1/25 : ℝ) - (1/100 : ℝ)) / 2 * (1 / ((13/37 : ℝ) + (56037/1000000 : ℝ)) + 1 / ((13/37 : ℝ) + (168699/1000000 : ℝ))) ≤ (656633/10000000 : ℝ) := by norm_num
  linarith

lemma as_lo1 : (166461/2500000 : ℝ) ≤ ∫ y in (1/100 : ℝ)..(1/25 : ℝ), 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) := by
  have h := as_mid_lower (1/3 : ℝ) (1/100 : ℝ) (1/25 : ℝ) (1/40 : ℝ) (1844447/500000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_U1 (by norm_num)
  have hb : (166461/2500000 : ℝ) ≤ ((1/25 : ℝ) - (1/100 : ℝ)) / ((1/3 : ℝ) + (1/40 : ℝ) + (1844447/500000 : ℝ) * (((1/100 : ℝ) + (1/25 : ℝ)) / 2)) := by norm_num
  linarith

lemma as_up2 : ∫ y in (1/25 : ℝ)..(9/100 : ℝ), 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) ≤ (215159/2500000 : ℝ) := by
  have h := as_trap_upper (13/37 : ℝ) (1/25 : ℝ) (9/100 : ℝ) (168699/1000000 : ℝ) (61339/200000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_L2 as_L3
  have hb : ((9/100 : ℝ) - (1/25 : ℝ)) / 2 * (1 / ((13/37 : ℝ) + (168699/1000000 : ℝ)) + 1 / ((13/37 : ℝ) + (61339/200000 : ℝ))) ≤ (215159/2500000 : ℝ) := by norm_num
  linarith

lemma as_lo2 : (86709/1000000 : ℝ) ≤ ∫ y in (1/25 : ℝ)..(9/100 : ℝ), 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) := by
  have h := as_mid_lower (1/3 : ℝ) (1/25 : ℝ) (9/100 : ℝ) (13/200 : ℝ) (2743201/1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_U2 (by norm_num)
  have hb : (86709/1000000 : ℝ) ≤ ((9/100 : ℝ) - (1/25 : ℝ)) / ((1/3 : ℝ) + (13/200 : ℝ) + (2743201/1000000 : ℝ) * (((1/25 : ℝ) + (9/100 : ℝ)) / 2)) := by norm_num
  linarith

lemma as_up3 : ∫ y in (9/100 : ℝ)..(4/25 : ℝ), 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) ≤ (967017/10000000 : ℝ) := by
  have h := as_trap_upper (13/37 : ℝ) (9/100 : ℝ) (4/25 : ℝ) (61339/200000 : ℝ) (45299/100000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_L3 as_L4
  have hb : ((4/25 : ℝ) - (9/100 : ℝ)) / 2 * (1 / ((13/37 : ℝ) + (61339/200000 : ℝ)) + 1 / ((13/37 : ℝ) + (45299/100000 : ℝ))) ≤ (967017/10000000 : ℝ) := by norm_num
  linarith

lemma as_lo3 : (972267/10000000 : ℝ) ≤ ∫ y in (9/100 : ℝ)..(4/25 : ℝ), 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) := by
  have h := as_mid_lower (1/3 : ℝ) (9/100 : ℝ) (4/25 : ℝ) (1/8 : ℝ) (1046533/500000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_U3 (by norm_num)
  have hb : (972267/10000000 : ℝ) ≤ ((4/25 : ℝ) - (9/100 : ℝ)) / ((1/3 : ℝ) + (1/8 : ℝ) + (1046533/500000 : ℝ) * (((9/100 : ℝ) + (4/25 : ℝ)) / 2)) := by norm_num
  linarith

lemma as_up4 : ∫ y in (4/25 : ℝ)..(1/4 : ℝ), 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) ≤ (1036403/10000000 : ℝ) := by
  have h := as_trap_upper (13/37 : ℝ) (4/25 : ℝ) (1/4 : ℝ) (45299/100000 : ℝ) (592167/1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_L4 as_L5
  have hb : ((1/4 : ℝ) - (4/25 : ℝ)) / 2 * (1 / ((13/37 : ℝ) + (45299/100000 : ℝ)) + 1 / ((13/37 : ℝ) + (592167/1000000 : ℝ))) ≤ (1036403/10000000 : ℝ) := by norm_num
  linarith

lemma as_lo4 : (1042623/10000000 : ℝ) ≤ ∫ y in (4/25 : ℝ)..(1/4 : ℝ), 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) := by
  have h := as_mid_lower (1/3 : ℝ) (4/25 : ℝ) (1/4 : ℝ) (41/200 : ℝ) (99047/62500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_U4 (by norm_num)
  have hb : (1042623/10000000 : ℝ) ≤ ((1/4 : ℝ) - (4/25 : ℝ)) / ((1/3 : ℝ) + (41/200 : ℝ) + (99047/62500 : ℝ) * (((4/25 : ℝ) + (1/4 : ℝ)) / 2)) := by norm_num
  linarith

lemma as_up5 : ∫ y in (1/4 : ℝ)..(9/25 : ℝ), 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) ≤ (68289/625000 : ℝ) := by
  have h := as_trap_upper (13/37 : ℝ) (1/4 : ℝ) (9/25 : ℝ) (592167/1000000 : ℝ) (727717/1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_L5 as_L6
  have hb : ((9/25 : ℝ) - (1/4 : ℝ)) / 2 * (1 / ((13/37 : ℝ) + (592167/1000000 : ℝ)) + 1 / ((13/37 : ℝ) + (727717/1000000 : ℝ))) ≤ (68289/625000 : ℝ) := by norm_num
  linarith

lemma as_lo5 : (137349/1250000 : ℝ) ≤ ∫ y in (1/4 : ℝ)..(9/25 : ℝ), 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) := by
  have h := as_mid_lower (1/3 : ℝ) (1/4 : ℝ) (9/25 : ℝ) (61/200 : ℝ) (237879/200000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_U5 (by norm_num)
  have hb : (137349/1250000 : ℝ) ≤ ((9/25 : ℝ) - (1/4 : ℝ)) / ((1/3 : ℝ) + (61/200 : ℝ) + (237879/200000 : ℝ) * (((1/4 : ℝ) + (9/25 : ℝ)) / 2)) := by norm_num
  linarith

lemma as_up6 : ∫ y in (9/25 : ℝ)..(49/100 : ℝ), 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) ≤ (1148181/10000000 : ℝ) := by
  have h := as_trap_upper (13/37 : ℝ) (9/25 : ℝ) (49/100 : ℝ) (727717/1000000 : ℝ) (839541/1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_L6 as_L7
  have hb : ((49/100 : ℝ) - (9/25 : ℝ)) / 2 * (1 / ((13/37 : ℝ) + (727717/1000000 : ℝ)) + 1 / ((13/37 : ℝ) + (839541/1000000 : ℝ))) ≤ (1148181/10000000 : ℝ) := by norm_num
  linarith

lemma as_lo6 : (1158653/10000000 : ℝ) ≤ ∫ y in (9/25 : ℝ)..(49/100 : ℝ), 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) := by
  have h := as_mid_lower (1/3 : ℝ) (9/25 : ℝ) (49/100 : ℝ) (17/40 : ℝ) (213917/250000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_U6 (by norm_num)
  have hb : (1158653/10000000 : ℝ) ≤ ((49/100 : ℝ) - (9/25 : ℝ)) / ((1/3 : ℝ) + (17/40 : ℝ) + (213917/250000 : ℝ) * (((9/25 : ℝ) + (49/100 : ℝ)) / 2)) := by norm_num
  linarith

lemma as_up7 : ∫ y in (49/100 : ℝ)..(16/25 : ℝ), 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) ≤ (243503/2000000 : ℝ) := by
  have h := as_trap_upper (13/37 : ℝ) (49/100 : ℝ) (16/25 : ℝ) (839541/1000000 : ℝ) (462367/500000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_L7 as_L8
  have hb : ((16/25 : ℝ) - (49/100 : ℝ)) / 2 * (1 / ((13/37 : ℝ) + (839541/1000000 : ℝ)) + 1 / ((13/37 : ℝ) + (462367/500000 : ℝ))) ≤ (243503/2000000 : ℝ) := by norm_num
  linarith

lemma as_lo7 : (1226021/10000000 : ℝ) ≤ ∫ y in (49/100 : ℝ)..(16/25 : ℝ), 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) := by
  have h := as_mid_lower (1/3 : ℝ) (49/100 : ℝ) (16/25 : ℝ) (113/200 : ℝ) (575463/1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_U7 (by norm_num)
  have hb : (1226021/10000000 : ℝ) ≤ ((16/25 : ℝ) - (49/100 : ℝ)) / ((1/3 : ℝ) + (113/200 : ℝ) + (575463/1000000 : ℝ) * (((49/100 : ℝ) + (16/25 : ℝ)) / 2)) := by norm_num
  linarith

lemma as_up8 : ∫ y in (16/25 : ℝ)..(81/100 : ℝ), 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) ≤ (1304227/10000000 : ℝ) := by
  have h := as_trap_upper (13/37 : ℝ) (16/25 : ℝ) (81/100 : ℝ) (462367/500000 : ℝ) (980673/1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_L8 as_L9
  have hb : ((81/100 : ℝ) - (16/25 : ℝ)) / 2 * (1 / ((13/37 : ℝ) + (462367/500000 : ℝ)) + 1 / ((13/37 : ℝ) + (980673/1000000 : ℝ))) ≤ (1304227/10000000 : ℝ) := by norm_num
  linarith

lemma as_lo8 : (329053/2500000 : ℝ) ≤ ∫ y in (16/25 : ℝ)..(81/100 : ℝ), 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) := by
  have h := as_mid_lower (1/3 : ℝ) (16/25 : ℝ) (81/100 : ℝ) (29/40 : ℝ) (160863/500000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_U8 (by norm_num)
  have hb : (329053/2500000 : ℝ) ≤ ((81/100 : ℝ) - (16/25 : ℝ)) / ((1/3 : ℝ) + (29/40 : ℝ) + (160863/500000 : ℝ) * (((16/25 : ℝ) + (81/100 : ℝ)) / 2)) := by norm_num
  linarith

lemma as_up9 : ∫ y in (81/100 : ℝ)..(1 : ℝ), 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) ≤ (1416201/10000000 : ℝ) := by
  have h := as_trap_upper (13/37 : ℝ) (81/100 : ℝ) (1 : ℝ) (980673/1000000 : ℝ) (1 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_L9 as_L10
  have hb : ((1 : ℝ) - (81/100 : ℝ)) / 2 * (1 / ((13/37 : ℝ) + (980673/1000000 : ℝ)) + 1 / ((13/37 : ℝ) + (1 : ℝ))) ≤ (1416201/10000000 : ℝ) := by norm_num
  linarith

lemma as_lo9 : (1429999/10000000 : ℝ) ≤ ∫ y in (81/100 : ℝ)..(1 : ℝ), 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) := by
  have h := as_mid_lower (1/3 : ℝ) (81/100 : ℝ) (1 : ℝ) (181/200 : ℝ) (99821/1000000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) as_U9 (by norm_num)
  have hb : (1429999/10000000 : ℝ) ≤ ((1 : ℝ) - (81/100 : ℝ)) / ((1/3 : ℝ) + (181/200 : ℝ) + (99821/1000000 : ℝ) * (((81/100 : ℝ) + (1 : ℝ)) / 2)) := by norm_num
  linarith

lemma as_upper_total : ∫ y in (0 : ℝ)..(1 : ℝ), 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) ≤ (4982239/5000000 : ℝ) := by
  have e0 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (13/37 : ℝ) (0 : ℝ) (1/100 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (13/37 : ℝ) (1/100 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (13/37 : ℝ) (1/100 : ℝ) (1/25 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (13/37 : ℝ) (1/25 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (13/37 : ℝ) (1/25 : ℝ) (9/100 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (13/37 : ℝ) (9/100 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e3 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (13/37 : ℝ) (9/100 : ℝ) (4/25 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (13/37 : ℝ) (4/25 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e4 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (13/37 : ℝ) (4/25 : ℝ) (1/4 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (13/37 : ℝ) (1/4 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e5 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (13/37 : ℝ) (1/4 : ℝ) (9/25 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (13/37 : ℝ) (9/25 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e6 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (13/37 : ℝ) (9/25 : ℝ) (49/100 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (13/37 : ℝ) (49/100 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e7 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (13/37 : ℝ) (49/100 : ℝ) (16/25 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (13/37 : ℝ) (16/25 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e8 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (13/37 : ℝ) (16/25 : ℝ) (81/100 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (13/37 : ℝ) (81/100 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have := as_up0
  have := as_up1
  have := as_up2
  have := as_up3
  have := as_up4
  have := as_up5
  have := as_up6
  have := as_up7
  have := as_up8
  have := as_up9

  linarith

lemma as_lower_total : ∫ y in (0 : ℝ)..(1 : ℝ), 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) ≥ (10051601/10000000 : ℝ) := by
  have e0 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (1/3 : ℝ) (0 : ℝ) (1/100 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (1/3 : ℝ) (1/100 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (1/3 : ℝ) (1/100 : ℝ) (1/25 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (1/3 : ℝ) (1/25 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (1/3 : ℝ) (1/25 : ℝ) (9/100 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (1/3 : ℝ) (9/100 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e3 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (1/3 : ℝ) (9/100 : ℝ) (4/25 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (1/3 : ℝ) (4/25 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e4 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (1/3 : ℝ) (4/25 : ℝ) (1/4 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (1/3 : ℝ) (1/4 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e5 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (1/3 : ℝ) (1/4 : ℝ) (9/25 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (1/3 : ℝ) (9/25 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e6 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (1/3 : ℝ) (9/25 : ℝ) (49/100 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (1/3 : ℝ) (49/100 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e7 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (1/3 : ℝ) (49/100 : ℝ) (16/25 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (1/3 : ℝ) (16/25 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have e8 := intervalIntegral.integral_add_adjacent_intervals
    (as_cont_on (1/3 : ℝ) (16/25 : ℝ) (81/100 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (as_cont_on (1/3 : ℝ) (81/100 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have := as_lo0
  have := as_lo1
  have := as_lo2
  have := as_lo3
  have := as_lo4
  have := as_lo5
  have := as_lo6
  have := as_lo7
  have := as_lo8
  have := as_lo9

  linarith

theorem solution (s : ℝ) (hs : SampleDrivenOS.Limit.IsAlphaStar s) :
    s ∈ Set.Icc (0.74 : ℝ) 0.75 := by
  obtain ⟨hs0, hs1, hint⟩ := hs
  have hfun : (fun y : ℝ => 1 / (y * (1 - Real.log y) + 1 / s - 1)) =
      fun y => 1 / (y * (1 - Real.log y) + (1 / s - 1)) := by
    funext y; ring
  rw [hfun] at hint
  have hcs : 0 < 1 / s - 1 := by
    have : 1 < 1 / s := by rw [lt_div_iff₀ hs0]; linarith
    linarith
  constructor
  · by_contra hlt
    have hlt' : s < 0.74 := lt_of_not_ge hlt
    have hc : (13/37 : ℝ) < 1 / s - 1 := by
      have : (50/37 : ℝ) < 1 / s := by
        rw [lt_div_iff₀ hs0]; norm_num at hlt' ⊢; linarith
      linarith
    have hmono : ∫ y in (0 : ℝ)..1, 1 / (y * (1 - Real.log y) + (1 / s - 1)) ≤
        ∫ y in (0 : ℝ)..1, 1 / (y * (1 - Real.log y) + (13/37 : ℝ)) :=
      intervalIntegral.integral_mono_on zero_le_one (as_cont_on _ 0 1 hcs le_rfl zero_le_one le_rfl)
        (as_cont_on _ 0 1 (by norm_num) le_rfl zero_le_one le_rfl) (fun y hy => by
          have := as_phi_nonneg y hy.1 hy.2
          exact one_div_le_one_div_of_le (by positivity) (by linarith))
    have := as_upper_total
    linarith
  · by_contra hlt
    have hlt' : 0.75 < s := lt_of_not_ge hlt
    have hc : 1 / s - 1 < (1/3 : ℝ) := by
      have : 1 / s < (4/3 : ℝ) := by
        rw [div_lt_iff₀ hs0]; norm_num at hlt' ⊢; linarith
      linarith
    have hmono : ∫ y in (0 : ℝ)..1, 1 / (y * (1 - Real.log y) + (1/3 : ℝ)) ≤
        ∫ y in (0 : ℝ)..1, 1 / (y * (1 - Real.log y) + (1 / s - 1)) :=
      intervalIntegral.integral_mono_on zero_le_one (as_cont_on _ 0 1 (by norm_num) le_rfl zero_le_one le_rfl)
        (as_cont_on _ 0 1 hcs le_rfl zero_le_one le_rfl) (fun y hy => by
          have := as_phi_nonneg y hy.1 hy.2
          exact one_div_le_one_div_of_le (by positivity) (by linarith))
    have := as_lower_total
    linarith
