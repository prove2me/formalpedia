-- Prove2me | solution 1 for SumProduct.sinc_power_integral_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:52:55.145732+00:00
-- url     : https://prove2.me/submissions/92bd23b6-b4f9-4fa7-9ac6-6fa06383282a

import Mathlib
import Definitions.Def_SumProduct_SincIntegral
import Theorems.Thm_SumProduct_integrable_sinc_pow
section
open MeasureTheory Set
namespace SumProduct
open Real
private lemma abs_sinc_le_inv_abs {t : ℝ} (ht : t ≠ 0) :
    |Real.sinc t| ≤ |t|⁻¹ := by
  rw [Real.sinc_of_ne_zero ht, abs_div]
  rw [div_le_iff₀ (by positivity)]
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  calc |Real.sin t| * |t| ≤ 1 * |t| := by
        gcongr; exact abs_sin_le_one t
    _ = |t| := by ring
private lemma abs_sinc_pow_le {t : ℝ} (ht : t ≠ 0) (N : ℕ) :
    |Real.sinc t| ^ N ≤ (|t|⁻¹) ^ N := by
  apply pow_le_pow_left₀ (abs_nonneg _) (abs_sinc_le_inv_abs ht)
private lemma abs_sinc_pow_le_inv_sq {t : ℝ} (ht : 1 ≤ |t|) {N : ℕ} (hN : 2 ≤ N) :
    |Real.sinc t| ^ N ≤ (|t| ^ 2)⁻¹ := by
  have ht0 : t ≠ 0 := by
    intro h; rw [h] at ht; simp at ht; linarith
  calc |Real.sinc t| ^ N ≤ (|t|⁻¹) ^ N := abs_sinc_pow_le ht0 N
    _ ≤ (|t|⁻¹) ^ 2 := by
        apply pow_le_pow_of_le_one (by positivity)
        · rw [inv_le_one_iff₀]; right; exact ht
        · exact hN
    _ = (|t| ^ 2)⁻¹ := by rw [inv_pow]
private lemma abs_sinc_pow_le_dom (t : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    |Real.sinc t| ^ N ≤ 2 * (1 + t ^ 2)⁻¹ := by
  rcases le_or_gt 1 |t| with ht | ht
  · have h1 : |Real.sinc t| ^ N ≤ (|t| ^ 2)⁻¹ := abs_sinc_pow_le_inv_sq ht hN
    have htsq : (1 : ℝ) ≤ t ^ 2 := by nlinarith [sq_abs t, ht, abs_nonneg t]
    have h2 : (|t| ^ 2)⁻¹ ≤ 2 * (1 + t ^ 2)⁻¹ := by
      rw [sq_abs]
      have hp1 : (0:ℝ) < t ^ 2 := by linarith
      have hp2 : (0:ℝ) < 1 + t ^ 2 := by linarith
      have e1 : (t ^ 2)⁻¹ = 1 / t ^ 2 := by rw [one_div]
      have e2 : (1 + t ^ 2)⁻¹ = 1 / (1 + t ^ 2) := by rw [one_div]
      rw [e1, e2, mul_one_div, div_le_div_iff₀ hp1 hp2]
      nlinarith [htsq]
    exact h1.trans h2
  · have hb : |Real.sinc t| ^ N ≤ 1 := by
      apply pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one t)
    have h2 : (1 : ℝ) ≤ 2 * (1 + t ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]
      nlinarith [sq_abs t, ht, abs_nonneg t]
    exact hb.trans h2
private lemma integrable_abs_sinc_pow {N : ℕ} (hN : 2 ≤ N) :
    Integrable (fun t : ℝ => |Real.sinc t| ^ N) := by
  apply Integrable.mono' (g := fun t => 2 * (1 + t ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul 2)
  · exact ((Real.continuous_sinc.abs).pow N).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_pow, abs_abs]
    exact abs_sinc_pow_le_dom t hN
private lemma abs_sinc_pow_le_rpow {R : ℝ} (hR : 0 < R) {t : ℝ} (ht : R < t) (N : ℕ) :
    |Real.sinc t| ^ N ≤ t ^ (-(N : ℝ)) := by
  have htpos : 0 < t := hR.trans ht
  have ht0 : t ≠ 0 := ne_of_gt htpos
  calc |Real.sinc t| ^ N ≤ (|t|⁻¹) ^ N := abs_sinc_pow_le ht0 N
    _ = (t⁻¹) ^ N := by rw [abs_of_pos htpos]
    _ = t ^ (-(N : ℝ)) := by
        rw [Real.rpow_neg htpos.le, Real.rpow_natCast, inv_pow]
private lemma integrableOn_rpow_neg_Ioi {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : 2 ≤ N) :
    IntegrableOn (fun t : ℝ => t ^ (-(N : ℝ))) (Ioi R) := by
  apply integrableOn_Ioi_rpow_of_lt _ hR
  have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith
private lemma tail_bound_Ioi {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : 2 ≤ N) :
    ∫ t in Ioi R, |Real.sinc t| ^ N ≤ R ^ (1 - (N : ℝ)) / ((N : ℝ) - 1) := by
  have hai : (-(N : ℝ)) < -1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hint_dom := integrableOn_rpow_neg_Ioi hR hN
  have hint_lhs : IntegrableOn (fun t : ℝ => |Real.sinc t| ^ N) (Ioi R) :=
    (integrable_abs_sinc_pow hN).integrableOn
  calc ∫ t in Ioi R, |Real.sinc t| ^ N
      ≤ ∫ t in Ioi R, t ^ (-(N : ℝ)) := by
        apply setIntegral_mono_on hint_lhs hint_dom measurableSet_Ioi
        intro t ht
        exact abs_sinc_pow_le_rpow hR (mem_Ioi.mp ht) N
    _ = -R ^ (-(N : ℝ) + 1) / (-(N : ℝ) + 1) := integral_Ioi_rpow_of_lt hai hR
    _ = R ^ (1 - (N : ℝ)) / ((N : ℝ) - 1) := by
        rw [show (-(N : ℝ) + 1) = (1 - (N : ℝ)) by ring,
          show ((N : ℝ) - 1) = -(1 - (N : ℝ)) by ring, div_neg, neg_div]
private lemma sinc_abs (t : ℝ) : Real.sinc |t| = Real.sinc t := by
  rcases abs_choice t with h | h
  · rw [h]
  · rw [h, Real.sinc_neg]
private lemma integral_sinc_pow_eq {N : ℕ} (_hN : 2 ≤ N) :
    ∫ t : ℝ, (Real.sinc t) ^ N = 2 * ∫ t in Ioi (0 : ℝ), (Real.sinc t) ^ N := by
  have h := integral_comp_abs (f := fun x : ℝ => (Real.sinc x) ^ N)
  rw [← h]
  congr 1
  ext t
  rw [sinc_abs]
private lemma integral_Ioi_split {N : ℕ} (hN : 2 ≤ N) {R : ℝ} (hR : 0 < R) :
    ∫ t in Ioi (0 : ℝ), (Real.sinc t) ^ N
      = (∫ t in Ioc (0 : ℝ) R, (Real.sinc t) ^ N) + ∫ t in Ioi R, (Real.sinc t) ^ N := by
  have hint : IntegrableOn (fun t : ℝ => (Real.sinc t) ^ N) (Ioi (0:ℝ)) :=
    (integrable_sinc_pow hN).integrableOn
  rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hR.le))]
  rw [Set.Ioc_union_Ioi_eq_Ioi hR.le]
private lemma J_zero : J 0 = 1 := by
  simp [J]
private lemma J_rec (N : ℕ) :
    (2 * (N : ℝ) + 3) * J (N + 1) = (2 * (N : ℝ) + 2) * J N := by
  -- FTC on `f u = u * (1 - u^2)^(N+1)`.
  set c : ℝ := 2 * ((N : ℝ) + 1) with hc
  have key : ∫ u in (0:ℝ)..1, ((1 - u ^ 2) ^ (N + 1)
      - c * (u ^ 2 * (1 - u ^ 2) ^ N)) = 0 := by
    have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun u => u * (1 - u ^ 2) ^ (N + 1))
          ((1 - u ^ 2) ^ (N + 1) - c * (u ^ 2 * (1 - u ^ 2) ^ N)) u := by
      intro u _
      have h1 : HasDerivAt (fun u : ℝ => (1 - u ^ 2) ^ (N + 1))
          ((↑(N + 1)) * (1 - u ^ 2) ^ N * (0 - 2 * u)) u := by
        have : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (0 - 2 * u) u :=
          (hasDerivAt_const u (1:ℝ)).sub (by simpa using hasDerivAt_pow 2 u)
        exact this.pow (N + 1)
      have h2 := (hasDerivAt_id u).mul h1
      convert h2 using 1 <;> try rfl
      simp only [hc, id_eq]
      push_cast
      rw [pow_succ]
      ring
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_
    · rw [this]; simp
    · apply Continuous.intervalIntegrable
      fun_prop
  -- Expand the integral.
  have hsplit : ∫ u in (0:ℝ)..1, ((1 - u ^ 2) ^ (N + 1)
      - c * (u ^ 2 * (1 - u ^ 2) ^ N))
      = J (N + 1) - c * ∫ u in (0:ℝ)..1, u ^ 2 * (1 - u ^ 2) ^ N := by
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul]; rfl
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
  -- `∫ u² (1-u²)^N = J N - J (N+1)`.
  have hsq : (∫ u in (0:ℝ)..1, u ^ 2 * (1 - u ^ 2) ^ N) = J N - J (N + 1) := by
    have : ∀ u : ℝ, u ^ 2 * (1 - u ^ 2) ^ N = (1 - u ^ 2) ^ N - (1 - u ^ 2) ^ (N + 1) := by
      intro u; rw [pow_succ]; ring
    rw [intervalIntegral.integral_congr (g := fun u => (1 - u ^ 2) ^ N - (1 - u ^ 2) ^ (N + 1))]
    · rw [intervalIntegral.integral_sub]
      · rfl
      · apply Continuous.intervalIntegrable; fun_prop
      · apply Continuous.intervalIntegrable; fun_prop
    · intro u _; exact this u
  rw [hsplit, hsq] at key
  rw [hc] at key
  nlinarith [key]
private lemma J_pos (N : ℕ) : 0 < J N := by
  rw [J]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply Continuous.intervalIntegrable; fun_prop
  · intro u hu
    have : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    positivity
  · norm_num
private lemma J_one : J 1 = 2 / 3 := by
  have h := J_rec 0
  rw [J_zero] at h
  push_cast at h
  linarith
private lemma J_two : J 2 = 8 / 15 := by
  have h := J_rec 1
  rw [J_one] at h
  push_cast at h
  linarith
private lemma J_sq_upper (N : ℕ) : ((N : ℝ) + 1) * (J N) ^ 2 ≤ 1 := by
  induction N with
  | zero => rw [J_zero]; norm_num
  | succ N ih =>
    have hrec := J_rec N
    have hJN := J_pos N
    have hJN1 := J_pos (N + 1)
    have hexp : J (N + 1) = (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 3) * J N := by
      field_simp at hrec ⊢
      linarith [hrec]
    rw [hexp]
    have hpos : (0:ℝ) < 2 * (N : ℝ) + 3 := by positivity
    push_cast
    rw [mul_pow, div_pow]
    have key : ((N : ℝ) + 1 + 1) * ((2 * (N : ℝ) + 2) ^ 2 / (2 * (N : ℝ) + 3) ^ 2) * J N ^ 2
        ≤ ((N : ℝ) + 1) * J N ^ 2 := by
      have hsqJ : (0:ℝ) ≤ J N ^ 2 := sq_nonneg _
      have hcoef : ((N : ℝ) + 1 + 1) * ((2 * (N : ℝ) + 2) ^ 2 / (2 * (N : ℝ) + 3) ^ 2)
          ≤ ((N : ℝ) + 1) := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ))]
      nlinarith [hsqJ, hcoef]
    calc ((N : ℝ) + 1 + 1) * ((2 * (N : ℝ) + 2) ^ 2 / (2 * (N : ℝ) + 3) ^ 2 * J N ^ 2)
        = ((N : ℝ) + 1 + 1) * ((2 * (N : ℝ) + 2) ^ 2 / (2 * (N : ℝ) + 3) ^ 2) * J N ^ 2 := by ring
      _ ≤ ((N : ℝ) + 1) * J N ^ 2 := key
      _ ≤ 1 := ih
private lemma J_le (N : ℕ) : J N ≤ 1 / Real.sqrt ((N : ℝ) + 1) := by
  have h := J_sq_upper N
  have hs : (0:ℝ) < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  rw [le_div_iff₀ hs]
  have hsq : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
  nlinarith [J_pos N, h, hsq, Real.sqrt_nonneg ((N : ℝ) + 1)]
private lemma J_sq_lower {N : ℕ} (hN : 2 ≤ N) : (5 : ℝ) / 4 ≤ (2 * (N : ℝ) + 1) * (J N) ^ 2 := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · -- base case N+1 = 2, i.e. N = 1
      interval_cases N
      · omega
      · rw [J_two]; norm_num
    · -- inductive step from N ≥ 2
      have ihN := ih hge
      have hrec := J_rec N
      have hJN := J_pos N
      have hexp : J (N + 1) = (2 * (N : ℝ) + 2) / (2 * (N : ℝ) + 3) * J N := by
        field_simp at hrec ⊢
        linarith [hrec]
      rw [hexp]
      push_cast
      rw [mul_pow, div_pow]
      have hcoef : (2 * (N : ℝ) + 1)
          ≤ (2 * ((N : ℝ) + 1) + 1)
            * ((2 * (N : ℝ) + 2) ^ 2 / (2 * (N : ℝ) + 3) ^ 2) := by
        rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
        nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ))]
      have hsqJ : (0:ℝ) ≤ J N ^ 2 := sq_nonneg _
      calc (5 : ℝ) / 4 ≤ (2 * (N : ℝ) + 1) * J N ^ 2 := ihN
        _ ≤ (2 * ((N : ℝ) + 1) + 1)
              * ((2 * (N : ℝ) + 2) ^ 2 / (2 * (N : ℝ) + 3) ^ 2) * J N ^ 2 := by
            nlinarith [hsqJ, hcoef]
        _ = (2 * ((N : ℝ) + 1) + 1)
              * (((2 * (N : ℝ) + 2) ^ 2 / (2 * (N : ℝ) + 3) ^ 2) * J N ^ 2) := by
            ring
private lemma J_ge {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt 5 / (2 * Real.sqrt (2 * (N : ℝ) + 1)) ≤ J N := by
  have h := J_sq_lower hN
  have hs : (0:ℝ) < Real.sqrt (2 * (N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_iff₀ (by positivity)]
  have hsq : Real.sqrt (2 * (N : ℝ) + 1) ^ 2 = 2 * (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  -- want √5 ≤ J N * (2 √(2N+1)); square both sides (both nonneg)
  have hrhs : (0:ℝ) ≤ J N * (2 * Real.sqrt (2 * (N : ℝ) + 1)) := by
    have := J_pos N; positivity
  have hsqr : (Real.sqrt 5) ^ 2 ≤ (J N * (2 * Real.sqrt (2 * (N : ℝ) + 1))) ^ 2 := by
    rw [h5, mul_pow, mul_pow, hsq]
    nlinarith [h, J_pos N]
  exact le_of_sq_le_sq hsqr hrhs
private lemma scaled_integral (N : ℕ) {R : ℝ} (hR : 0 < R) :
    ∫ t in Ioc (0:ℝ) R, (1 - (t / R) ^ 2) ^ N = R * J N := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hRinv : R⁻¹ ≠ 0 := inv_ne_zero hRne
  rw [← intervalIntegral.integral_of_le hR.le]
  have hsub := intervalIntegral.integral_comp_mul_left (a := 0) (b := R)
    (fun s : ℝ => (1 - s ^ 2) ^ N) hRinv
  simp only [mul_zero, inv_mul_cancel₀ hRne, inv_inv] at hsub
  have step : (∫ t in (0:ℝ)..R, (1 - (R⁻¹ * t) ^ 2) ^ N) = R * J N := by
    rw [hsub, J, smul_eq_mul]
  rw [← step]
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  rw [div_eq_inv_mul]
private lemma sin_ge_sub_cube {t : ℝ} (ht : 0 ≤ t) : t - t ^ 3 / 6 ≤ Real.sin t := by
  set g : ℝ → ℝ := fun x => Real.sin x - x + x ^ 3 / 6 with hg
  have hderiv : ∀ x : ℝ, HasDerivAt g (Real.cos x - 1 + x ^ 2 / 2) x := by
    intro x
    have : HasDerivAt g (Real.cos x - 1 + 3 * x ^ 2 / 6) x := by
      rw [hg]
      have h1 : HasDerivAt (fun x => Real.sin x) (Real.cos x) x := Real.hasDerivAt_sin x
      have h2 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
      have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / 6) (3 * x ^ 2 / 6) x := by
        have := (hasDerivAt_pow 3 x).div_const 6
        simpa using this
      convert (h1.sub h2).add h3 using 1 <;> rfl
    convert this using 1
    ring
  have hgdiff : Differentiable ℝ g := fun x => (hderiv x).differentiableAt
  have hgderiv_nonneg : ∀ x, 0 ≤ deriv g x := by
    intro x
    rw [(hderiv x).deriv]
    have := Real.one_sub_sq_div_two_le_cos (x := x)
    linarith
  have hmono : Monotone g := monotone_of_deriv_nonneg hgdiff hgderiv_nonneg
  have hg0 : g 0 = 0 := by rw [hg]; simp
  have := hmono ht
  rw [hg0] at this
  simp only [hg] at this
  linarith
private lemma sinc_pow_ge_near {N : ℕ} {t : ℝ} (ht0 : 0 < t) (ht6 : t ≤ Real.sqrt 6) :
    (1 - (t / Real.sqrt 6) ^ 2) ^ N ≤ (Real.sinc t) ^ N := by
  have hs6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hs6pos : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have heq : (t / Real.sqrt 6) ^ 2 = t ^ 2 / 6 := by
    rw [div_pow, hs6]
  have htsq : t ^ 2 ≤ 6 := by nlinarith [ht0, ht6, hs6, hs6pos]
  have hnn : 0 ≤ 1 - (t / Real.sqrt 6) ^ 2 := by
    rw [heq]; nlinarith [htsq]
  have hsinc_ge : 1 - (t / Real.sqrt 6) ^ 2 ≤ Real.sinc t := by
    rw [Real.sinc_of_ne_zero (ne_of_gt ht0), heq]
    rw [le_div_iff₀ ht0]
    have := sin_ge_sub_cube ht0.le
    have hsplit : (1 - t ^ 2 / 6) * t = t - t ^ 3 / 6 := by ring
    rw [hsplit]
    exact this
  apply pow_le_pow_left₀ hnn hsinc_ge
private lemma sinc_nonneg_of_mem {t : ℝ} (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi) :
    0 ≤ Real.sinc t := by
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]; simp
  · rw [Real.sinc_of_ne_zero (ne_of_gt h)]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht0 htπ) ht0
private lemma sinc_le_cos_half {t : ℝ} (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi) :
    Real.sinc t ≤ Real.cos (t / 2) := by
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]; simp
  · have htne : t ≠ 0 := ne_of_gt h
    have hcos : 0 ≤ Real.cos (t / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
    have hsplit : Real.sinc t = Real.sinc (t / 2) * Real.cos (t / 2) := by
      rw [Real.sinc_of_ne_zero htne, Real.sinc_of_ne_zero (by positivity : t / 2 ≠ 0)]
      rw [show t = 2 * (t / 2) by ring, Real.sin_two_mul]
      field_simp
    rw [hsplit]
    calc Real.sinc (t / 2) * Real.cos (t / 2)
        ≤ 1 * Real.cos (t / 2) := by
          apply mul_le_mul_of_nonneg_right (Real.sinc_le_one _) hcos
      _ = Real.cos (t / 2) := one_mul _
private lemma sinc_pow_le_near {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi) :
    (Real.sinc t) ^ N ≤ (1 - (t / (Real.pi * Real.sqrt 2)) ^ 2) ^ N := by
  apply pow_le_pow_left₀ (sinc_nonneg_of_mem ht0 htπ)
  -- sinc t ≤ cos(t/2) ≤ 1 - 2/π²·(t/2)² = 1 - (t/(π√2))²
  have h1 : Real.sinc t ≤ Real.cos (t / 2) := sinc_le_cos_half ht0 htπ
  have h2 : Real.cos (t / 2) ≤ 1 - 2 / Real.pi ^ 2 * (t / 2) ^ 2 := by
    apply Real.cos_le_one_sub_mul_cos_sq
    rw [abs_le]
    constructor <;> [linarith [Real.pi_pos]; linarith]
  have h3 : 1 - 2 / Real.pi ^ 2 * (t / 2) ^ 2 = 1 - (t / (Real.pi * Real.sqrt 2)) ^ 2 := by
    have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have : (t / (Real.pi * Real.sqrt 2)) ^ 2 = t ^ 2 / (Real.pi ^ 2 * 2) := by
      rw [div_pow, mul_pow, hsqrt2]
    rw [this]
    field_simp
  linarith [h1, h2, h3]
private lemma upper_near {N : ℕ} (hN : 2 ≤ N) :
    ∫ t in Ioc (0:ℝ) Real.pi, (Real.sinc t) ^ N ≤ (Real.pi * Real.sqrt 2) * J N := by
  set R' : ℝ := Real.pi * Real.sqrt 2 with hR'
  have hR'pos : 0 < R' := by
    rw [hR']; positivity
  have hπR' : Real.pi ≤ R' := by
    rw [hR']
    nlinarith [Real.pi_pos, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
      Real.one_le_sqrt.mpr (show (1:ℝ) ≤ 2 by norm_num)]
  -- the comparison function
  have hmeas : MeasurableSet (Ioc (0:ℝ) Real.pi) := measurableSet_Ioc
  have hint_sinc : IntegrableOn (fun t : ℝ => (Real.sinc t) ^ N) (Ioc (0:ℝ) Real.pi) :=
    (integrable_sinc_pow hN).integrableOn
  have hint_comp_R' : IntegrableOn (fun t : ℝ => (1 - (t / R') ^ 2) ^ N) (Ioc (0:ℝ) R') := by
    apply Continuous.integrableOn_Ioc
    fun_prop
  have hint_comp : IntegrableOn (fun t : ℝ => (1 - (t / R') ^ 2) ^ N) (Ioc (0:ℝ) Real.pi) :=
    hint_comp_R'.mono_set (Ioc_subset_Ioc_right hπR')
  -- Step 1: sinc^N ≤ comparison on (0,π]
  have step1 : ∫ t in Ioc (0:ℝ) Real.pi, (Real.sinc t) ^ N
      ≤ ∫ t in Ioc (0:ℝ) Real.pi, (1 - (t / R') ^ 2) ^ N := by
    apply setIntegral_mono_on hint_sinc hint_comp hmeas
    intro t ht
    exact sinc_pow_le_near ht.1.le ht.2
  -- Step 2: extend domain to (0,R']
  have step2 : ∫ t in Ioc (0:ℝ) Real.pi, (1 - (t / R') ^ 2) ^ N
      ≤ ∫ t in Ioc (0:ℝ) R', (1 - (t / R') ^ 2) ^ N := by
    apply setIntegral_mono_set hint_comp_R'
    · filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (0:ℝ) R'))] with t ht
      have hnn : 0 ≤ 1 - (t / R') ^ 2 := by
        have h1 : (t / R') ^ 2 ≤ 1 := by
          rw [div_pow, div_le_one (by positivity)]
          nlinarith [ht.1, ht.2, hR'pos]
        linarith
      positivity
    · exact HasSubset.Subset.eventuallyLE (Ioc_subset_Ioc_right hπR')
  -- Step 3: scaled integral value
  have step3 : ∫ t in Ioc (0:ℝ) R', (1 - (t / R') ^ 2) ^ N = R' * J N :=
    scaled_integral N hR'pos
  calc ∫ t in Ioc (0:ℝ) Real.pi, (Real.sinc t) ^ N
      ≤ ∫ t in Ioc (0:ℝ) Real.pi, (1 - (t / R') ^ 2) ^ N := step1
    _ ≤ ∫ t in Ioc (0:ℝ) R', (1 - (t / R') ^ 2) ^ N := step2
    _ = R' * J N := step3
private lemma sqrt_le_pow {c : ℝ} (hc : Real.sqrt 2 ≤ c) {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt (N : ℝ) ≤ c ^ (N - 1) := by
  have hcpos : 0 < c := lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num)) hc
  have hc2 : 2 ≤ c ^ 2 := by
    nlinarith [hc, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    have hMpos : (1:ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hstep : Real.sqrt ((M : ℝ) + 1) ≤ c * Real.sqrt (M : ℝ) := by
      rw [show c = Real.sqrt (c ^ 2) by rw [Real.sqrt_sq hcpos.le]]
      rw [← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      nlinarith [hMpos, hc2]
    calc Real.sqrt ((↑(M + 1) : ℝ))
        = Real.sqrt ((M : ℝ) + 1) := by push_cast; ring_nf
      _ ≤ c * Real.sqrt (M : ℝ) := hstep
      _ ≤ c * c ^ (M - 1) := by exact mul_le_mul_of_nonneg_left ih hcpos.le
      _ = c ^ (M + 1 - 1) := by
          rw [show M + 1 - 1 = M by omega, ← pow_succ']
          congr 1
          omega
private lemma tail_term_le {c : ℝ} (hc : Real.sqrt 2 ≤ c) {N : ℕ} (hN : 2 ≤ N) :
    c ^ (1 - (N : ℝ)) / ((N : ℝ) - 1) ≤ 1 / Real.sqrt (N : ℝ) := by
  have hcpos : 0 < c := lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num)) hc
  have hNc : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hN1 : (0:ℝ) < (N : ℝ) - 1 := by linarith
  -- c^(1-N) = (c^(N-1))⁻¹ in rpow, equals natural power inverse
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]; push_cast; ring
  have hrpow : c ^ (1 - (N : ℝ)) = (c ^ (N - 1))⁻¹ := by
    rw [show (1 - (N : ℝ)) = -(((N - 1 : ℕ) : ℝ)) by rw [hcast]; ring]
    rw [Real.rpow_neg hcpos.le, Real.rpow_natCast]
  rw [hrpow]
  have hpow_pos : 0 < c ^ (N - 1) := by positivity
  rw [div_le_div_iff₀ hN1 hsqrtN]
  -- (c^(N-1))⁻¹ * √N ≤ 1 * (N-1)
  rw [inv_mul_eq_div, div_le_iff₀ hpow_pos, one_mul]
  have h1 : Real.sqrt (N : ℝ) ≤ c ^ (N - 1) := sqrt_le_pow hc (by omega)
  nlinarith [h1, hpow_pos, hN1]
private lemma lower_near {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt 6 * J N ≤ ∫ t in Ioc (0:ℝ) (Real.sqrt 6), (Real.sinc t) ^ N := by
  have hs6pos : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hmeas : MeasurableSet (Ioc (0:ℝ) (Real.sqrt 6)) := measurableSet_Ioc
  have hint_sinc : IntegrableOn (fun t : ℝ => (Real.sinc t) ^ N) (Ioc (0:ℝ) (Real.sqrt 6)) :=
    (integrable_sinc_pow hN).integrableOn
  have hint_comp : IntegrableOn (fun t : ℝ => (1 - (t / Real.sqrt 6) ^ 2) ^ N)
      (Ioc (0:ℝ) (Real.sqrt 6)) := by
    apply Continuous.integrableOn_Ioc; fun_prop
  have hscaled : ∫ t in Ioc (0:ℝ) (Real.sqrt 6), (1 - (t / Real.sqrt 6) ^ 2) ^ N
      = Real.sqrt 6 * J N := scaled_integral N hs6pos
  rw [← hscaled]
  apply setIntegral_mono_on hint_comp hint_sinc hmeas
  intro t ht
  exact sinc_pow_ge_near ht.1 ht.2
private lemma tail_le_abs {R : ℝ} {N : ℕ} (hN : 2 ≤ N) :
    ∫ t in Ioi R, (Real.sinc t) ^ N ≤ ∫ t in Ioi R, |Real.sinc t| ^ N := by
  apply setIntegral_mono_on (integrable_sinc_pow hN).integrableOn
    (integrable_abs_sinc_pow hN).integrableOn measurableSet_Ioi
  intro t _
  calc (Real.sinc t) ^ N ≤ |(Real.sinc t) ^ N| := le_abs_self _
    _ = |Real.sinc t| ^ N := abs_pow _ _
private lemma neg_abs_le_tail {R : ℝ} {N : ℕ} (hN : 2 ≤ N) :
    - ∫ t in Ioi R, |Real.sinc t| ^ N ≤ ∫ t in Ioi R, (Real.sinc t) ^ N := by
  rw [neg_le]
  rw [← integral_neg]
  apply setIntegral_mono_on ((integrable_sinc_pow hN).neg).integrableOn
    (integrable_abs_sinc_pow hN).integrableOn measurableSet_Ioi
  intro t _
  calc -(Real.sinc t) ^ N ≤ |(Real.sinc t) ^ N| := neg_le_abs _
    _ = |Real.sinc t| ^ N := abs_pow _ _
private lemma tail_nonneg_even {R : ℝ} {N : ℕ} (_hN : 2 ≤ N) (hev : Even N) :
    0 ≤ ∫ t in Ioi R, (Real.sinc t) ^ N := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro t _
  exact hev.pow_nonneg _
private lemma three_sqrt_le_pow {N : ℕ} (hN : 3 ≤ N) :
    3 * Real.sqrt (N : ℝ) ≤ Real.sqrt 6 ^ (N - 1) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h3 : Real.sqrt 6 ^ (3 - 1) = 6 := by
      norm_num [Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)]
    rw [h3]
    have : Real.sqrt 3 ≤ 2 := by
      rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ)=2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h3c : ((3:ℕ):ℝ) = 3 := by norm_num
    rw [h3c]; nlinarith [this]
  | succ M hM ih =>
    have hMpos : (3:ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hs6pos : (0:ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
    have hs6sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have hstep : Real.sqrt ((M : ℝ) + 1) ≤ Real.sqrt 6 * Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      nlinarith [hMpos, hs6sq]
    calc 3 * Real.sqrt ((↑(M + 1) : ℝ))
        = 3 * Real.sqrt ((M : ℝ) + 1) := by push_cast; ring_nf
      _ ≤ 3 * (Real.sqrt 6 * Real.sqrt (M : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = Real.sqrt 6 * (3 * Real.sqrt (M : ℝ)) := by ring
      _ ≤ Real.sqrt 6 * Real.sqrt 6 ^ (M - 1) := mul_le_mul_of_nonneg_left ih hs6pos.le
      _ = Real.sqrt 6 ^ (M + 1 - 1) := by
          rw [show M + 1 - 1 = M by omega, ← pow_succ']
          congr 1; omega
private lemma odd_tail_small {N : ℕ} (hN : 3 ≤ N) :
    Real.sqrt (N:ℝ) * (Real.sqrt 6 ^ (1 - (N : ℝ)) / ((N : ℝ) - 1)) ≤ 1 / 6 := by
  have hs6pos : (0:ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hNc : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hsqrtN : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]; push_cast; ring
  have hrpow : Real.sqrt 6 ^ (1 - (N : ℝ)) = (Real.sqrt 6 ^ (N - 1))⁻¹ := by
    rw [show (1 - (N : ℝ)) = -(((N - 1 : ℕ) : ℝ)) by rw [hcast]; ring]
    rw [Real.rpow_neg hs6pos.le, Real.rpow_natCast]
  rw [hrpow]
  have hpow_pos : 0 < Real.sqrt 6 ^ (N - 1) := by positivity
  have h3 : 3 * Real.sqrt (N:ℝ) ≤ Real.sqrt 6 ^ (N - 1) := three_sqrt_le_pow hN
  have hN1 : (2:ℝ) ≤ (N:ℝ) - 1 := by linarith
  -- the denominator pow*(N-1) ≥ 6 √N
  have hden : 6 * Real.sqrt (N:ℝ) ≤ Real.sqrt 6 ^ (N - 1) * ((N : ℝ) - 1) := by
    calc 6 * Real.sqrt (N:ℝ) = (3 * Real.sqrt (N:ℝ)) * 2 := by ring
      _ ≤ Real.sqrt 6 ^ (N - 1) * ((N : ℝ) - 1) := by
          apply mul_le_mul h3 hN1 (by norm_num) hpow_pos.le
  have hprod_pos : 0 < Real.sqrt 6 ^ (N - 1) * ((N : ℝ) - 1) := by positivity
  have hlhs : Real.sqrt (N:ℝ) * ((Real.sqrt 6 ^ (N - 1))⁻¹ / ((N : ℝ) - 1))
      = Real.sqrt (N:ℝ) / (Real.sqrt 6 ^ (N - 1) * ((N : ℝ) - 1)) := by
    rw [div_eq_mul_inv, ← mul_inv]
    ring
  rw [hlhs, div_le_iff₀ hprod_pos]
  -- √N ≤ 1/6 * (pow * (N-1))
  nlinarith [hden, hsqrtN]
private lemma sqrtN_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Real.sqrt (N : ℝ) := by
  apply Real.sqrt_pos.mpr
  have : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  linarith
private lemma upper_bound {N : ℕ} (hN : 2 ≤ N) :
    ∫ t : ℝ, (Real.sinc t) ^ N ≤ 5 * Real.pi / Real.sqrt (N : ℝ) := by
  have hsqrtN := sqrtN_pos hN
  have hNc : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hπ2 : Real.sqrt 2 ≤ Real.pi := by
    have : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    linarith [Real.pi_gt_three]
  rw [integral_sinc_pow_eq hN, integral_Ioi_split hN Real.pi_pos]
  -- bound the two pieces
  have hnear : ∫ t in Ioc (0:ℝ) Real.pi, (Real.sinc t) ^ N
      ≤ (Real.pi * Real.sqrt 2) * (1 / Real.sqrt ((N:ℝ) + 1)) := by
    refine (upper_near hN).trans ?_
    apply mul_le_mul_of_nonneg_left (J_le N)
    positivity
  have htail : ∫ t in Ioi Real.pi, (Real.sinc t) ^ N ≤ 1 / Real.sqrt (N : ℝ) := by
    refine (tail_le_abs hN).trans ?_
    refine (tail_bound_Ioi Real.pi_pos hN).trans ?_
    exact tail_term_le hπ2 hN
  -- combine
  have hsqrtN1 : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hinv : 1 / Real.sqrt ((N:ℝ) + 1) ≤ 1 / Real.sqrt (N : ℝ) := by
    apply one_div_le_one_div_of_le hsqrtN hsqrtN1
  have hnear2 : ∫ t in Ioc (0:ℝ) Real.pi, (Real.sinc t) ^ N
      ≤ (Real.pi * Real.sqrt 2) * (1 / Real.sqrt (N : ℝ)) := by
    refine hnear.trans ?_
    apply mul_le_mul_of_nonneg_left hinv
    positivity
  have hcomb : 2 * ((∫ t in Ioc (0:ℝ) Real.pi, (Real.sinc t) ^ N)
      + ∫ t in Ioi Real.pi, (Real.sinc t) ^ N)
      ≤ 2 * ((Real.pi * Real.sqrt 2) * (1 / Real.sqrt (N : ℝ)) + 1 / Real.sqrt (N : ℝ)) := by
    apply mul_le_mul_of_nonneg_left (add_le_add hnear2 htail) (by norm_num)
  refine hcomb.trans ?_
  -- 2(π√2/√N + 1/√N) ≤ 5π/√N
  rw [div_eq_mul_one_div (5 * Real.pi)]
  have hfac : 2 * ((Real.pi * Real.sqrt 2) * (1 / Real.sqrt (N : ℝ)) + 1 / Real.sqrt (N : ℝ))
      = (2 * (Real.pi * Real.sqrt 2) + 2) * (1 / Real.sqrt (N : ℝ)) := by ring
  rw [hfac]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  -- 2π√2 + 2 ≤ 5π
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3/2:ℝ) = Real.sqrt ((3/2)^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  nlinarith [hs2, Real.pi_gt_three, Real.pi_pos]
private lemma near_lb {N : ℕ} (hN : 2 ≤ N) :
    Real.sqrt 30 / Real.sqrt (2 * (N:ℝ) + 1) ≤ 2 * Real.sqrt 6 * J N := by
  have hJ := J_ge hN
  have hr : 0 < Real.sqrt (2 * (N:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h630 : Real.sqrt 6 * Real.sqrt 5 = Real.sqrt 30 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  -- 2√6 * J N ≥ 2√6 * √5/(2√(2N+1)) = √30/√(2N+1)
  calc Real.sqrt 30 / Real.sqrt (2 * (N:ℝ) + 1)
      = 2 * Real.sqrt 6 * (Real.sqrt 5 / (2 * Real.sqrt (2 * (N:ℝ) + 1))) := by
        rw [← h630]; field_simp
    _ ≤ 2 * Real.sqrt 6 * J N := by
        apply mul_le_mul_of_nonneg_left hJ (by positivity)
private lemma lower_bound {N : ℕ} (hN : 2 ≤ N) :
    Real.pi / Real.sqrt (N : ℝ) ≤ ∫ t : ℝ, (Real.sinc t) ^ N := by
  have hsqrtN := sqrtN_pos hN
  have hNc : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hr : 0 < Real.sqrt (2 * (N:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hrsq : Real.sqrt (2 * (N:ℝ) + 1) ^ 2 = 2 * (N:ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hsNsq : Real.sqrt (N:ℝ) ^ 2 = (N:ℝ) := Real.sq_sqrt (by linarith)
  have h30 : Real.sqrt 30 ^ 2 = 30 := Real.sq_sqrt (by norm_num)
  rw [integral_sinc_pow_eq hN,
    integral_Ioi_split hN (Real.sqrt_pos.mpr (show (0:ℝ) < 6 by norm_num))]
  -- near lower bound
  have hnear : Real.sqrt 30 / Real.sqrt (2 * (N:ℝ) + 1)
      ≤ 2 * ∫ t in Ioc (0:ℝ) (Real.sqrt 6), (Real.sinc t) ^ N := by
    refine (near_lb hN).trans ?_
    have hln := lower_near hN
    have : 2 * Real.sqrt 6 * J N = 2 * (Real.sqrt 6 * J N) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left hln (by norm_num)
  rcases Nat.even_or_odd N with hev | hodd
  · -- even N: tail ≥ 0
    have htail : (0:ℝ) ≤ 2 * ∫ t in Ioi (Real.sqrt 6), (Real.sinc t) ^ N := by
      have := tail_nonneg_even (R := Real.sqrt 6) hN hev
      linarith
    -- combine: 2*(near + tail) ≥ 2*near ≥ √30/√(2N+1) ≥ π/√N
    have hkey : Real.pi / Real.sqrt (N:ℝ) ≤ Real.sqrt 30 / Real.sqrt (2 * (N:ℝ) + 1) := by
      rw [div_le_div_iff₀ hsqrtN hr]
      -- π * √(2N+1) ≤ √30 * √N; square and use π² ≤ 10.
      have hpi2 : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      have hsq : (Real.pi * Real.sqrt (2 * (N:ℝ) + 1)) ^ 2
          ≤ (Real.sqrt 30 * Real.sqrt (N:ℝ)) ^ 2 := by
        rw [mul_pow, mul_pow, hrsq, hsNsq, h30]
        nlinarith [hpi2, Real.pi_pos, hNc]
      exact le_of_sq_le_sq hsq (by positivity)
    have hfinal : 2 * ((∫ t in Ioc (0:ℝ) (Real.sqrt 6), (Real.sinc t) ^ N)
        + ∫ t in Ioi (Real.sqrt 6), (Real.sinc t) ^ N)
        = 2 * (∫ t in Ioc (0:ℝ) (Real.sqrt 6), (Real.sinc t) ^ N)
          + 2 * ∫ t in Ioi (Real.sqrt 6), (Real.sinc t) ^ N := by ring
    rw [hfinal]
    linarith [hkey, hnear, htail]
  · -- odd N: N ≥ 3, tail ≥ -1/3 / √N
    have hN3 : 3 ≤ N := by
      rcases hodd with ⟨k, rfl⟩; omega
    -- tail lower bound
    have htailbd : ∫ t in Ioi (Real.sqrt 6), |Real.sinc t| ^ N
        ≤ Real.sqrt 6 ^ (1 - (N : ℝ)) / ((N : ℝ) - 1) :=
      tail_bound_Ioi (Real.sqrt_pos.mpr (show (0:ℝ) < 6 by norm_num)) hN
    have htail : - (Real.sqrt 6 ^ (1 - (N : ℝ)) / ((N : ℝ) - 1))
        ≤ ∫ t in Ioi (Real.sqrt 6), (Real.sinc t) ^ N := by
      refine le_trans ?_ (neg_abs_le_tail (R := Real.sqrt 6) hN)
      apply neg_le_neg htailbd
    have htail_small :
        Real.sqrt (N:ℝ) * (Real.sqrt 6 ^ (1 - (N : ℝ)) / ((N : ℝ) - 1)) ≤ 1 / 6 :=
      odd_tail_small hN3
    -- near constant for odd N: √30/√(2N+1) ≥ √(90/7)/√N  (since 2N+1 ≤ 7N/3)
    have hfinal : 2 * ((∫ t in Ioc (0:ℝ) (Real.sqrt 6), (Real.sinc t) ^ N)
        + ∫ t in Ioi (Real.sqrt 6), (Real.sinc t) ^ N)
        = 2 * (∫ t in Ioc (0:ℝ) (Real.sqrt 6), (Real.sinc t) ^ N)
          + 2 * ∫ t in Ioi (Real.sqrt 6), (Real.sinc t) ^ N := by ring
    rw [hfinal]
    -- It suffices: π/√N ≤ √30/√(2N+1) - 2*(tailterm)
    have hgoal : Real.pi / Real.sqrt (N:ℝ)
        ≤ Real.sqrt 30 / Real.sqrt (2 * (N:ℝ) + 1)
          - 2 * (Real.sqrt 6 ^ (1 - (N : ℝ)) / ((N : ℝ) - 1)) := by
      -- multiply through by √N
      have hNc3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN3
      -- √30/√(2N+1) * √N ≥ √(90/7) since 2N+1 ≤ 7N/3
      have hnear_const : Real.sqrt (90 / 7)
          ≤ Real.sqrt 30 / Real.sqrt (2 * (N:ℝ) + 1) * Real.sqrt (N:ℝ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr]
        have hsq : (Real.sqrt (90/7) * Real.sqrt (2 * (N:ℝ) + 1)) ^ 2
            ≤ (Real.sqrt 30 * Real.sqrt (N:ℝ)) ^ 2 := by
          rw [mul_pow, mul_pow, hrsq, hsNsq, h30,
            Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 90/7)]
          nlinarith [hNc3]
        exact le_of_sq_le_sq hsq (by positivity)
      -- assemble using √(90/7) - 1/3 ≥ π
      have hconst : Real.pi ≤ Real.sqrt (90/7) - 1/3 := by
        have h907 : Real.sqrt (90/7) ^ 2 = 90/7 := Real.sq_sqrt (by norm_num)
        have hs907 : (3.4833 : ℝ) ≤ Real.sqrt (90/7) := by
          nlinarith [h907, Real.sqrt_nonneg (90/7)]
        nlinarith [Real.pi_lt_d2, hs907]
      rw [div_le_iff₀ hsqrtN]
      -- goal: π ≤ (√30/√(2N+1) - 2*tailterm) * √N
      have hexpand : (Real.sqrt 30 / Real.sqrt (2 * (N:ℝ) + 1)
          - 2 * (Real.sqrt 6 ^ (1 - (N : ℝ)) / ((N : ℝ) - 1))) * Real.sqrt (N:ℝ)
          = (Real.sqrt 30 / Real.sqrt (2 * (N:ℝ) + 1)) * Real.sqrt (N:ℝ)
            - 2 * (Real.sqrt (N:ℝ)
              * (Real.sqrt 6 ^ (1 - (N : ℝ)) / ((N : ℝ) - 1))) := by
        ring
      rw [hexpand]
      linarith [hnear_const, htail_small, hconst]
    linarith [hgoal, hnear, htail,
      mul_le_mul_of_nonneg_left htail (by norm_num : (0:ℝ) ≤ 2)]
end SumProduct
end

set_option autoImplicit true
open MeasureTheory Set
open SumProduct
open Real
namespace SumProduct
theorem _root_.solution (N : ℕ) (hN : 2 ≤ N) :
    Real.pi / Real.sqrt (N : ℝ) ≤ ∫ t : ℝ, (Real.sinc t) ^ N ∧
      ∫ t : ℝ, (Real.sinc t) ^ N ≤ 5 * Real.pi / Real.sqrt (N : ℝ) :=
  ⟨lower_bound hN, upper_bound hN⟩
end SumProduct
