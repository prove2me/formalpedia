-- Prove2me | solution 1 for TaoFivePrimes.eta1_L2_sq
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T22:12:40.353392+00:00
-- url     : https://prove2.me/submissions/e1a2ba83-a1d0-46c1-a846-dcaf748f70ac

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

end TaoEta1

theorem solution : (∫ t : ℝ, TaoFivePrimes.eta1 t ^ 2) = 2/3 :=
  TaoEta1.eta1_L2sq
