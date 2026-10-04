-- Prove2me | solution 1 for TaoFivePrimes.eta1_mul_deriv_L1
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T22:17:08.330322+00:00
-- url     : https://prove2.me/submissions/7b06a9cf-3d8d-452d-ad97-c356d820617c

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory
open TaoFivePrimes

namespace TaoEta1

theorem infDist_Icc {a b t : ℝ} (hab : a ≤ b) :
    Metric.infDist t (Set.Icc a b) = max 0 (max (a - t) (t - b)) := by
  refine le_antisymm ?_ ?_
  · rcases le_total t a with h | h
    · calc Metric.infDist t (Set.Icc a b) ≤ dist t a :=
            Metric.infDist_le_dist_of_mem (Set.left_mem_Icc.mpr hab)
        _ = a - t := by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; ring
        _ ≤ _ := le_max_of_le_right (le_max_left _ _)
    · rcases le_total t b with h2 | h2
      · rw [Metric.infDist_zero_of_mem (Set.mem_Icc.mpr ⟨h, h2⟩)]
        exact le_max_left _ _
      · calc Metric.infDist t (Set.Icc a b) ≤ dist t b :=
              Metric.infDist_le_dist_of_mem (Set.right_mem_Icc.mpr hab)
          _ = t - b := by rw [Real.dist_eq, abs_of_nonneg (by linarith)]
          _ ≤ _ := le_max_of_le_right (le_max_right _ _)
  · rw [Metric.le_infDist (⟨a, Set.left_mem_Icc.mpr hab⟩ : (Set.Icc a b).Nonempty)]
    rintro y ⟨hy1, hy2⟩
    rw [Real.dist_eq]
    refine max_le (abs_nonneg _) (max_le ?_ ?_) <;>
      rcases abs_cases (t - y) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith

theorem eta1_eq (t : ℝ) : eta1 t = max 0 (min 1 (min (10*t - 1) (9 - 10*t))) := by
  unfold eta1
  rw [infDist_Icc (by norm_num : (1/5:ℝ) ≤ 4/5)]
  rcases le_total t (1/5 : ℝ) with h1 | h1
  · have hm : max ((1/5:ℝ) - t) (t - 4/5) = 1/5 - t := max_eq_left (by linarith)
    rw [hm, max_eq_right (by linarith : (0:ℝ) ≤ 1/5 - t)]
    rw [min_eq_left (by linarith : (10:ℝ)*t - 1 ≤ 9 - 10*t),
      min_eq_right (by linarith : (10:ℝ)*t - 1 ≤ 1)]
    ring_nf
  · rcases le_total t (4/5 : ℝ) with h2 | h2
    · have hm : max (0:ℝ) (max ((1/5:ℝ) - t) (t - 4/5)) = 0 :=
        max_eq_left (max_le (by linarith) (by linarith))
      rw [hm, min_eq_left (le_min (by linarith) (by linarith))]
      norm_num
    · have hm : max ((1/5:ℝ) - t) (t - 4/5) = t - 4/5 := max_eq_right (by linarith)
      rw [hm, max_eq_right (by linarith : (0:ℝ) ≤ t - 4/5)]
      rw [min_eq_right (by linarith : (9:ℝ) - 10*t ≤ 10*t - 1),
        min_eq_right (by linarith : (9:ℝ) - 10*t ≤ 1)]
      ring_nf

theorem eta1_zero_left {t : ℝ} (h : t ≤ 1/10) : eta1 t = 0 := by
  rw [eta1_eq, max_eq_left]
  exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (by linarith))

theorem eta1_zero_right {t : ℝ} (h : 9/10 ≤ t) : eta1 t = 0 := by
  rw [eta1_eq, max_eq_left]
  exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (by linarith))

theorem eta1_ramp_left {t : ℝ} (h1 : 1/10 ≤ t) (h2 : t ≤ 1/5) : eta1 t = 10*t - 1 := by
  rw [eta1_eq, min_eq_left (by linarith : (10:ℝ)*t - 1 ≤ 9 - 10*t),
    min_eq_right (by linarith : (10:ℝ)*t - 1 ≤ 1), max_eq_right (by linarith)]

theorem eta1_plateau {t : ℝ} (h1 : 1/5 ≤ t) (h2 : t ≤ 4/5) : eta1 t = 1 := by
  rw [eta1_eq, min_eq_left (le_min (by linarith) (by linarith)), max_eq_right (by norm_num)]

theorem eta1_ramp_right {t : ℝ} (h1 : 4/5 ≤ t) (h2 : t ≤ 9/10) : eta1 t = 9 - 10*t := by
  rw [eta1_eq, min_eq_right (by linarith : (9:ℝ) - 10*t ≤ 10*t - 1),
    min_eq_right (by linarith : (9:ℝ) - 10*t ≤ 1), max_eq_right (by linarith)]

/-- **Tao, Section 8, the symmetry of `η₁`.**  `η₁(1-t) = η₁(t)`. -/
theorem eta1_symm (t : ℝ) : eta1 (1 - t) = eta1 t := by
  rw [eta1_eq, eta1_eq, show (10:ℝ) * (1 - t) - 1 = 9 - 10*t by ring,
    show (9:ℝ) - 10 * (1 - t) = 10*t - 1 by ring, min_comm (9 - 10*t) (10*t - 1)]

/-- **Tao, Section 8, `‖η₁‖_{L^∞(ℝ)} = 1`.** -/
theorem eta1_sup : (∀ t : ℝ, eta1 t ≤ 1) ∧ eta1 (1/2) = 1 := by
  refine ⟨fun t => ?_, eta1_plateau (by norm_num) (by norm_num)⟩
  rw [eta1_eq]
  exact max_le (by norm_num) (min_le_left _ _)


theorem eta1_continuous : Continuous eta1 := by
  have h : eta1 = fun t : ℝ => max 0 (min 1 (min (10*t - 1) (9 - 10*t))) := funext eta1_eq
  rw [h]
  fun_prop

theorem eta1_nonneg (t : ℝ) : 0 ≤ eta1 t := le_max_left _ _

private theorem split3 (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (1/10:ℝ)..(9/10), f t)
      = (∫ t in (1/10:ℝ)..(1/5), f t) + (∫ t in (1/5:ℝ)..(4/5), f t)
        + (∫ t in (4/5:ℝ)..(9/10), f t) := by
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

private theorem to_interval (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ t ∈ (Set.Icc (1/10:ℝ) (9/10))ᶜ, f t = 0) :
    (∫ t : ℝ, f t) = ∫ t in (1/10:ℝ)..(9/10), f t := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1/10:ℝ) ≤ 9/10)]

private theorem poly_int {f f' : ℝ → ℝ} (a b : ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hc : Continuous f') : (∫ t in a..b, f' t) = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hf t) (hc.intervalIntegrable _ _)

private theorem e_ramp_left : (∫ t in (1/10:ℝ)..(1/5), (10*t - 1)) = 1/20 := by
  rw [poly_int (f := fun u : ℝ => 5*u^2 - u) _ _
    (fun t => by
      have h : HasDerivAt (fun u : ℝ => 5*u^2 - u) (5 * (2 * t ^ 1) - 1) t :=
        ((hasDerivAt_pow 2 t).const_mul (5:ℝ)).sub (hasDerivAt_id t)
      convert h using 1
      ring)
    (by fun_prop)]
  norm_num

private theorem e_plateau : (∫ _t in (1/5:ℝ)..(4/5), (1:ℝ)) = 3/5 := by
  rw [intervalIntegral.integral_const]; norm_num

private theorem e_ramp_right : (∫ t in (4/5:ℝ)..(9/10), (9 - 10*t)) = 1/20 := by
  rw [poly_int (f := fun u : ℝ => 9*u - 5*u^2) _ _
    (fun t => by
      have h : HasDerivAt (fun u : ℝ => 9*u - 5*u^2) (9 * 1 - 5 * (2 * t ^ 1)) t :=
        ((hasDerivAt_id t).const_mul (9:ℝ)).sub ((hasDerivAt_pow 2 t).const_mul (5:ℝ))
      convert h using 1
      ring)
    (by fun_prop)]
  norm_num

private theorem e_sq_left : (∫ t in (1/10:ℝ)..(1/5), (100*t^2 - 20*t + 1)) = 1/30 := by
  rw [poly_int (f := fun u : ℝ => 100*u^3/3 - 10*u^2 + u) _ _
    (fun t => by
      have h : HasDerivAt (fun u : ℝ => 100*u^3/3 - 10*u^2 + u)
          (100 * (3 * t ^ 2) / 3 - 10 * (2 * t ^ 1) + 1) t :=
        ((((hasDerivAt_pow 3 t).const_mul (100:ℝ)).div_const 3).sub
          ((hasDerivAt_pow 2 t).const_mul (10:ℝ))).add (hasDerivAt_id t)
      convert h using 1
      ring)
    (by fun_prop)]
  norm_num

private theorem e_sq_right : (∫ t in (4/5:ℝ)..(9/10), (100*t^2 - 180*t + 81)) = 1/30 := by
  rw [poly_int (f := fun u : ℝ => 100*u^3/3 - 90*u^2 + 81*u) _ _
    (fun t => by
      have h : HasDerivAt (fun u : ℝ => 100*u^3/3 - 90*u^2 + 81*u)
          (100 * (3 * t ^ 2) / 3 - 90 * (2 * t ^ 1) + 81 * 1) t :=
        ((((hasDerivAt_pow 3 t).const_mul (100:ℝ)).div_const 3).sub
          ((hasDerivAt_pow 2 t).const_mul (90:ℝ))).add ((hasDerivAt_id t).const_mul (81:ℝ))
      convert h using 1
      ring)
    (by fun_prop)]
  norm_num

/-- **Tao, Section 8, `‖η₁‖_{L¹(ℝ)} = 7/10`.** -/
theorem eta1_L1 : (∫ t : ℝ, eta1 t) = 7/10 := by
  have hz : ∀ t ∈ (Set.Icc (1/10:ℝ) (9/10))ᶜ, eta1 t = 0 := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · exact eta1_zero_left (le_of_lt h)
    · exact eta1_zero_right (le_of_lt h)
  rw [to_interval eta1 eta1_continuous hz, split3 eta1 eta1_continuous]
  have h1 : (∫ t in (1/10:ℝ)..(1/5), eta1 t) = ∫ t in (1/10:ℝ)..(1/5), (10*t - 1) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1/10:ℝ) ≤ 1/5), Set.mem_Icc] at ht
    exact eta1_ramp_left ht.1 ht.2
  have h2 : (∫ t in (1/5:ℝ)..(4/5), eta1 t) = ∫ _t in (1/5:ℝ)..(4/5), (1:ℝ) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1/5:ℝ) ≤ 4/5), Set.mem_Icc] at ht
    exact eta1_plateau ht.1 ht.2
  have h3 : (∫ t in (4/5:ℝ)..(9/10), eta1 t) = ∫ t in (4/5:ℝ)..(9/10), (9 - 10*t) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (4/5:ℝ) ≤ 9/10), Set.mem_Icc] at ht
    exact eta1_ramp_right ht.1 ht.2
  rw [h1, h2, h3, e_ramp_left, e_plateau, e_ramp_right]
  norm_num

/-- **Tao, Section 8, `‖η₁‖_{L²(ℝ)} = √(2/3)`,** in the form `∫ η₁² = 2/3`. -/
theorem eta1_L2sq : (∫ t : ℝ, eta1 t ^ 2) = 2/3 := by
  have hcont : Continuous (fun t : ℝ => eta1 t ^ 2) := eta1_continuous.pow 2
  have hz : ∀ t ∈ (Set.Icc (1/10:ℝ) (9/10))ᶜ, eta1 t ^ 2 = 0 := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [eta1_zero_left (le_of_lt h)]; ring
    · rw [eta1_zero_right (le_of_lt h)]; ring
  rw [to_interval _ hcont hz, split3 _ hcont]
  have h1 : (∫ t in (1/10:ℝ)..(1/5), eta1 t ^ 2)
      = ∫ t in (1/10:ℝ)..(1/5), (100*t^2 - 20*t + 1) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1/10:ℝ) ≤ 1/5), Set.mem_Icc] at ht
    rw [eta1_ramp_left ht.1 ht.2]; ring
  have h2 : (∫ t in (1/5:ℝ)..(4/5), eta1 t ^ 2) = ∫ _t in (1/5:ℝ)..(4/5), (1:ℝ) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1/5:ℝ) ≤ 4/5), Set.mem_Icc] at ht
    rw [eta1_plateau ht.1 ht.2]; ring
  have h3 : (∫ t in (4/5:ℝ)..(9/10), eta1 t ^ 2)
      = ∫ t in (4/5:ℝ)..(9/10), (100*t^2 - 180*t + 81) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (4/5:ℝ) ≤ 9/10), Set.mem_Icc] at ht
    rw [eta1_ramp_right ht.1 ht.2]; ring
  rw [h1, h2, h3, e_sq_left, e_plateau, e_sq_right]
  norm_num


/-- **Tao, Section 8, `‖η₁'‖_{L^∞(ℝ)} = 10`,** in the form that `η₁` is `10`-Lipschitz. -/
theorem eta1_lipschitz : LipschitzWith 10 eta1 := by
  have h : eta1 = fun t : ℝ => max 0 (min 1 (min (10*t - 1) (9 - 10*t))) := funext eta1_eq
  rw [h]
  have h1 : LipschitzWith 10 (fun t : ℝ => 10*t - 1) := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    simp only [Real.dist_eq]
    rw [show (10*x - 1) - (10*y - 1) = 10*(x-y) by ring, abs_mul]
    norm_num
  have h2 : LipschitzWith 10 (fun t : ℝ => 9 - 10*t) := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    simp only [Real.dist_eq]
    rw [show (9 - 10*x) - (9 - 10*y) = -(10*(x-y)) by ring, abs_neg, abs_mul]
    norm_num
  simpa using ((h1.min h2).const_min 1).const_max 0


/-! ### The derivative of `η₁` -/

theorem deriv_lo {t : ℝ} (h : t < 1/10) : deriv eta1 t = 0 := by
  have hev : eta1 =ᶠ[nhds t] (fun _ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds h] with u hu
    exact eta1_zero_left (le_of_lt hu)
  rw [hev.deriv_eq, deriv_const]

theorem deriv_hi {t : ℝ} (h : 9/10 < t) : deriv eta1 t = 0 := by
  have hev : eta1 =ᶠ[nhds t] (fun _ => (0:ℝ)) := by
    filter_upwards [Ioi_mem_nhds h] with u hu
    exact eta1_zero_right (le_of_lt hu)
  rw [hev.deriv_eq, deriv_const]

theorem deriv_pl {t : ℝ} (h1 : 1/5 < t) (h2 : t < 4/5) : deriv eta1 t = 0 := by
  have hev : eta1 =ᶠ[nhds t] (fun _ => (1:ℝ)) := by
    filter_upwards [Ioo_mem_nhds h1 h2] with u hu
    exact eta1_plateau (le_of_lt hu.1) (le_of_lt hu.2)
  rw [hev.deriv_eq, deriv_const]

theorem deriv_r1 {t : ℝ} (h1 : 1/10 < t) (h2 : t < 1/5) : deriv eta1 t = 10 := by
  have hev : eta1 =ᶠ[nhds t] (fun u => 10*u - 1) := by
    filter_upwards [Ioo_mem_nhds h1 h2] with u hu
    exact eta1_ramp_left (le_of_lt hu.1) (le_of_lt hu.2)
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun u : ℝ => 10*u - 1) (10 * 1) t :=
    ((hasDerivAt_id t).const_mul (10:ℝ)).sub_const 1
  rw [hd.deriv]; ring

theorem deriv_r2 {t : ℝ} (h1 : 4/5 < t) (h2 : t < 9/10) : deriv eta1 t = -10 := by
  have hev : eta1 =ᶠ[nhds t] (fun u => 9 - 10*u) := by
    filter_upwards [Ioo_mem_nhds h1 h2] with u hu
    exact eta1_ramp_right (le_of_lt hu.1) (le_of_lt hu.2)
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun u : ℝ => 9 - 10*u) (0 - 10 * 1) t :=
    (hasDerivAt_const t (9:ℝ)).sub ((hasDerivAt_id t).const_mul (10:ℝ))
  rw [hd.deriv]; ring

private theorem ae_off {S : Set ℝ} (hS : volume S = 0) {f g : ℝ → ℝ} {a b : ℝ}
    (h : ∀ t, t ∉ S → t ∈ Set.uIoc a b → f t = g t) :
    ∀ᵐ t, t ∈ Set.uIoc a b → f t = g t := by
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hS] with t ht hmem
  exact h t ht hmem

private theorem ii_congr {f g : ℝ → ℝ} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (h : ∀ᵐ t, t ∈ Set.uIoc a b → f t = g t) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff] at hg ⊢
  refine hg.congr ?_
  show ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)), g t = f t
  rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [h] with t ht hmem
  exact (ht hmem).symm

private theorem null_pt (c : ℝ) : volume ({c} : Set ℝ) = 0 := measure_singleton c

private theorem split_at (f : ℝ → ℝ)
    (h1 : IntervalIntegrable f volume (1/10) (1/5))
    (h2 : IntervalIntegrable f volume (1/5) (4/5))
    (h3 : IntervalIntegrable f volume (4/5) (9/10)) :
    (∫ t in (1/10:ℝ)..(9/10), f t)
      = (∫ t in (1/10:ℝ)..(1/5), f t) + (∫ t in (1/5:ℝ)..(4/5), f t)
        + (∫ t in (4/5:ℝ)..(9/10), f t) := by
  rw [intervalIntegral.integral_add_adjacent_intervals h1 h2,
    intervalIntegral.integral_add_adjacent_intervals (h1.trans h2) h3]

/-- **Tao, Section 8, `‖η₁'‖_{L¹(ℝ)} = 2`.** -/
theorem eta1_deriv_L1 : (∫ t : ℝ, |deriv eta1 t|) = 2 := by
  have hz : ∀ t ∈ (Set.Icc (1/10:ℝ) (9/10))ᶜ, |deriv eta1 t| = 0 := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [deriv_lo h, abs_zero]
    · rw [deriv_hi h, abs_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1/10:ℝ) ≤ 9/10)]
  have a1 : ∀ᵐ t, t ∈ Set.uIoc (1/10:ℝ) (1/5) → |deriv eta1 t| = 10 := by
    refine ae_off (null_pt (1/5:ℝ)) (fun t ht hmem => ?_)
    rw [Set.uIoc_of_le (by norm_num : (1/10:ℝ) ≤ 1/5), Set.mem_Ioc] at hmem
    simp only [Set.mem_singleton_iff] at ht
    rw [deriv_r1 hmem.1 (lt_of_le_of_ne hmem.2 ht)]
    norm_num
  have a2 : ∀ᵐ t, t ∈ Set.uIoc (1/5:ℝ) (4/5) → |deriv eta1 t| = 0 := by
    refine ae_off (null_pt (4/5:ℝ)) (fun t ht hmem => ?_)
    rw [Set.uIoc_of_le (by norm_num : (1/5:ℝ) ≤ 4/5), Set.mem_Ioc] at hmem
    simp only [Set.mem_singleton_iff] at ht
    rw [deriv_pl hmem.1 (lt_of_le_of_ne hmem.2 ht), abs_zero]
  have a3 : ∀ᵐ t, t ∈ Set.uIoc (4/5:ℝ) (9/10) → |deriv eta1 t| = 10 := by
    refine ae_off (null_pt (9/10:ℝ)) (fun t ht hmem => ?_)
    rw [Set.uIoc_of_le (by norm_num : (4/5:ℝ) ≤ 9/10), Set.mem_Ioc] at hmem
    simp only [Set.mem_singleton_iff] at ht
    rw [deriv_r2 hmem.1 (lt_of_le_of_ne hmem.2 ht)]
    norm_num
  rw [split_at _ (ii_congr intervalIntegrable_const a1)
      (ii_congr intervalIntegrable_const a2) (ii_congr intervalIntegrable_const a3),
    intervalIntegral.integral_congr_ae a1, intervalIntegral.integral_congr_ae a2,
    intervalIntegral.integral_congr_ae a3, intervalIntegral.integral_const,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  norm_num

/-- **Tao, Section 8, `‖η₁ η₁'‖_{L¹(ℝ)} = 1`.** -/
theorem eta1_mul_deriv_L1 : (∫ t : ℝ, |eta1 t * deriv eta1 t|) = 1 := by
  have hz : ∀ t ∈ (Set.Icc (1/10:ℝ) (9/10))ᶜ, |eta1 t * deriv eta1 t| = 0 := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [deriv_lo h, mul_zero, abs_zero]
    · rw [deriv_hi h, mul_zero, abs_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1/10:ℝ) ≤ 9/10)]
  have a1 : ∀ᵐ t, t ∈ Set.uIoc (1/10:ℝ) (1/5) → |eta1 t * deriv eta1 t| = 10*(10*t - 1) := by
    refine ae_off (null_pt (1/5:ℝ)) (fun t ht hmem => ?_)
    rw [Set.uIoc_of_le (by norm_num : (1/10:ℝ) ≤ 1/5), Set.mem_Ioc] at hmem
    simp only [Set.mem_singleton_iff] at ht
    have hlt : t < 1/5 := lt_of_le_of_ne hmem.2 ht
    rw [deriv_r1 hmem.1 hlt, eta1_ramp_left (le_of_lt hmem.1) (le_of_lt hlt),
      abs_of_nonneg (by nlinarith [hmem.1])]
    ring
  have a2 : ∀ᵐ t, t ∈ Set.uIoc (1/5:ℝ) (4/5) → |eta1 t * deriv eta1 t| = 0 := by
    refine ae_off (null_pt (4/5:ℝ)) (fun t ht hmem => ?_)
    rw [Set.uIoc_of_le (by norm_num : (1/5:ℝ) ≤ 4/5), Set.mem_Ioc] at hmem
    simp only [Set.mem_singleton_iff] at ht
    rw [deriv_pl hmem.1 (lt_of_le_of_ne hmem.2 ht), mul_zero, abs_zero]
  have a3 : ∀ᵐ t, t ∈ Set.uIoc (4/5:ℝ) (9/10) → |eta1 t * deriv eta1 t| = 10*(9 - 10*t) := by
    refine ae_off (null_pt (9/10:ℝ)) (fun t ht hmem => ?_)
    rw [Set.uIoc_of_le (by norm_num : (4/5:ℝ) ≤ 9/10), Set.mem_Ioc] at hmem
    simp only [Set.mem_singleton_iff] at ht
    have hlt : t < 9/10 := lt_of_le_of_ne hmem.2 ht
    rw [deriv_r2 hmem.1 hlt, eta1_ramp_right (le_of_lt hmem.1) (le_of_lt hlt),
      abs_of_nonpos (by nlinarith [hmem.1, hlt])]
    ring
  rw [split_at _
      (ii_congr ((by fun_prop : Continuous (fun t : ℝ => 10*(10*t - 1))).intervalIntegrable _ _) a1)
      (ii_congr intervalIntegrable_const a2)
      (ii_congr ((by fun_prop : Continuous (fun t : ℝ => 10*(9 - 10*t))).intervalIntegrable _ _) a3),
    intervalIntegral.integral_congr_ae a1, intervalIntegral.integral_congr_ae a2,
    intervalIntegral.integral_congr_ae a3, intervalIntegral.integral_const]
  have e1 : (∫ t in (1/10:ℝ)..(1/5), 10*(10*t - 1)) = 1/2 := by
    rw [show (fun t : ℝ => 10*(10*t - 1)) = (fun t : ℝ => 10*(10*t) - 10) from
      funext (fun t => by ring)]
    rw [poly_int (f := fun u : ℝ => 50*u^2 - 10*u) _ _
      (fun t => by
        have h : HasDerivAt (fun u : ℝ => 50*u^2 - 10*u) (50 * (2 * t ^ 1) - 10 * 1) t :=
          ((hasDerivAt_pow 2 t).const_mul (50:ℝ)).sub ((hasDerivAt_id t).const_mul (10:ℝ))
        convert h using 1
        ring)
      (by fun_prop)]
    norm_num
  have e3 : (∫ t in (4/5:ℝ)..(9/10), 10*(9 - 10*t)) = 1/2 := by
    rw [poly_int (f := fun u : ℝ => 90*u - 50*u^2) _ _
      (fun t => by
        have h : HasDerivAt (fun u : ℝ => 90*u - 50*u^2) (90 * 1 - 50 * (2 * t ^ 1)) t :=
          ((hasDerivAt_id t).const_mul (90:ℝ)).sub ((hasDerivAt_pow 2 t).const_mul (50:ℝ))
        convert h using 1
        ring)
      (by fun_prop)]
    norm_num
  rw [e1, e3]
  norm_num

end TaoEta1

theorem solution :
    (∫ t : ℝ, |TaoFivePrimes.eta1 t * deriv TaoFivePrimes.eta1 t|) = 1 :=
  TaoEta1.eta1_mul_deriv_L1
