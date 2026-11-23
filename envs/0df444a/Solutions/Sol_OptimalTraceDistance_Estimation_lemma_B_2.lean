-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T09:45:14.133185+00:00
-- url     : https://prove2.me/submissions/d034125f-0d9b-4481-b16d-6e9cfe404743

import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_B_1
import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_2_3
import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_2_5

open MeasureTheory
open scoped Real
open scoped BigOperators Matrix ENNReal

noncomputable section
namespace OTDJackson
open OptimalTraceDistance.Estimation

lemma int_cos_nat (n : ℕ) (hn : n ≠ 0) (a b : ℝ) :
    ∫ x in a..b, Real.cos (n * x) = (Real.sin (n * b) - Real.sin (n * a)) / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hn', integral_cos, smul_eq_mul]
  field_simp

lemma int_cos_period (n : ℕ) (hn : n ≠ 0) : ∫ x in (-π)..π, Real.cos (n * x) = 0 := by
  rw [int_cos_nat n hn, mul_neg, Real.sin_neg, Real.sin_nat_mul_pi]; simp

lemma cos_mul_cos' (k l : ℕ) (x : ℝ) :
    Real.cos (k * x) * Real.cos (l * x) =
      (Real.cos (((k + l : ℕ) : ℝ) * x) + Real.cos (((k - l : ℤ) : ℝ) * x)) / 2 := by
  push_cast
  rw [show ((k:ℝ) + l) * x = k * x + l * x by ring, show ((k:ℝ) - l) * x = k * x - l * x by ring,
    Real.cos_add, Real.cos_sub]; ring

lemma int_cos_int (m : ℤ) (hm : m ≠ 0) : ∫ x in (-π)..π, Real.cos (m * x) = 0 := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · push_cast; exact int_cos_period n (by rintro rfl; simp at hm)
  · push_cast
    simp only [neg_mul, Real.cos_neg]
    exact int_cos_period n (by rintro rfl; simp at hm)

lemma intInt_cos (m : ℝ) (a b : ℝ) : IntervalIntegrable (fun x => Real.cos (m * x)) volume a b :=
  (by fun_prop : Continuous fun x => Real.cos (m * x)).intervalIntegrable _ _

lemma orth (k l : ℕ) :
    ∫ x in (-π)..π, Real.cos (k * x) * Real.cos (l * x) =
      if k = l then (if k = 0 then 2 * π else π) else 0 := by
  simp only [cos_mul_cos']
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (intInt_cos _ _ _) (intInt_cos _ _ _)]
  split_ifs with h1 h2
  · subst h1; subst h2; simp; ring
  · subst h1
    rw [int_cos_period (k + k) (by omega)]; simp
  · rw [int_cos_period (k + l) (by omega), int_cos_int (k - l : ℤ) (by omega)]; simp


lemma sign_monotone : Monotone sign := by
  intro a b hab
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have : sign a = -1 := by simp [sign, ha]
    rw [this]; unfold sign; split_ifs <;> norm_num
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · linarith
    · exact le_rfl
    · simp [sign, not_lt.mpr hb.le, hb.ne']
  · have hb : 0 < b := lt_of_lt_of_le ha hab
    simp [sign, not_lt.mpr ha.le, ha.ne', not_lt.mpr hb.le, hb.ne']

lemma abs_sign_le (x : ℝ) : |sign x| ≤ 1 := by
  unfold sign; split_ifs <;> norm_num

def sfun (φ : ℝ) : ℝ := sign (Real.cos φ)

lemma sfun_measurable : Measurable sfun :=
  sign_monotone.measurable.comp Real.continuous_cos.measurable

lemma abs_sfun_le (x : ℝ) : |sfun x| ≤ 1 := abs_sign_le _

lemma bdd_intInt {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  refine ⟨IntegrableOn.of_bound (by simp) hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => by simpa using hb x)),
    IntegrableOn.of_bound (by simp) hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => by simpa using hb x))⟩

lemma sfun_periodic : Function.Periodic sfun (2 * π) := by
  intro x; simp [sfun, Real.cos_add_two_pi]

lemma sfun_even (x : ℝ) : sfun (-x) = sfun x := by simp [sfun]

lemma sfun_pos {x : ℝ} (h1 : -(π/2) < x) (h2 : x < π/2) : sfun x = 1 := by
  have := Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩
  simp [sfun, sign, not_lt.mpr this.le, this.ne']

lemma sfun_neg {x : ℝ} (h1 : π/2 < x) (h2 : x < π + π/2) : sfun x = -1 := by
  have := Real.cos_neg_of_pi_div_two_lt_of_lt h1 h2
  simp [sfun, sign, this]

lemma ae_ne (c : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
  rw [ae_iff]; simp

lemma intInt_cos_sfun (m : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun u => Real.cos (m * u) * sfun u) volume a b :=
  bdd_intInt ((by fun_prop : Continuous fun u => Real.cos (m * u)).measurable.mul sfun_measurable)
    (C := 1) (fun x => by
      show |Real.cos (m * x) * sfun x| ≤ 1
      rw [abs_mul]; exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (abs_sfun_le x)) a b

lemma intInt_sin_sfun (m : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun u => Real.sin (m * u) * sfun u) volume a b :=
  bdd_intInt ((by fun_prop : Continuous fun u => Real.sin (m * u)).measurable.mul sfun_measurable)
    (C := 1) (fun x => by
      show |Real.sin (m * x) * sfun x| ≤ 1
      rw [abs_mul]; exact mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (abs_sfun_le x)) a b

lemma int_cos_sfun (k : ℕ) (hk : k ≠ 0) :
    ∫ u in (-π)..π, Real.cos (k * u) * sfun u = 4 * Real.sin (k * π / 2) / k := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hp := Real.pi_pos
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := -(π/2)) (intInt_cos_sfun _ _ _)
    (intInt_cos_sfun _ _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := -(π/2)) (b := π/2) (intInt_cos_sfun _ _ _)
    (intInt_cos_sfun _ _ _)]
  have e1 : ∫ u in (-π)..(-(π/2)), Real.cos (k * u) * sfun u =
      ∫ u in (-π)..(-(π/2)), -Real.cos (k * u) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne (-(π/2))] with x hx hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have hlt : x < -(π/2) := lt_of_le_of_ne hmem.2 hx
    rw [← sfun_even, sfun_neg (by linarith) (by linarith [hmem.1])]; ring
  have e2 : ∫ u in (-(π/2))..(π/2), Real.cos (k * u) * sfun u =
      ∫ u in (-(π/2))..(π/2), Real.cos (k * u) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne (π/2)] with x hx hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have hlt : x < π/2 := lt_of_le_of_ne hmem.2 hx
    rw [sfun_pos hmem.1 hlt]; ring
  have e3 : ∫ u in (π/2)..π, Real.cos (k * u) * sfun u = ∫ u in (π/2)..π, -Real.cos (k * u) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne (π/2)] with x hx hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    rw [sfun_neg hmem.1 (by linarith [hmem.2])]; ring
  rw [e1, e2, e3, intervalIntegral.integral_neg, intervalIntegral.integral_neg, int_cos_nat k hk,
    int_cos_nat k hk, int_cos_nat k hk]
  have s1 : Real.sin (k * π) = 0 := Real.sin_nat_mul_pi k
  have s2 : Real.sin (k * -π) = 0 := by rw [mul_neg, Real.sin_neg, s1, neg_zero]
  have s3 : Real.sin (k * -(π/2)) = - Real.sin (k * π / 2) := by
    rw [mul_neg, Real.sin_neg, mul_div_assoc]
  have s4 : Real.sin (k * (π/2)) = Real.sin (k * π / 2) := by rw [mul_div_assoc]
  rw [s1, s2, s3, s4]
  field_simp; ring

lemma int_sin_sfun (k : ℕ) : ∫ u in (-π)..π, Real.sin (k * u) * sfun u = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
    (fun u => Real.sin (k * u) * sfun u)
  simp only [neg_neg, mul_neg, Real.sin_neg, sfun_even, neg_mul] at h
  rw [intervalIntegral.integral_neg] at h
  linarith


lemma int_sfun : ∫ u in (-π)..π, sfun u = 0 := by
  have h := int_cos_sfun 1 one_ne_zero
  have hp := Real.pi_pos
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := -(π/2))
    (bdd_intInt sfun_measurable abs_sfun_le _ _) (bdd_intInt sfun_measurable abs_sfun_le _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := -(π/2)) (b := π/2)
    (bdd_intInt sfun_measurable abs_sfun_le _ _) (bdd_intInt sfun_measurable abs_sfun_le _ _)]
  have e1 : ∫ u in (-π)..(-(π/2)), sfun u = ∫ u in (-π)..(-(π/2)), (-1:ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne (-(π/2))] with x hx hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have hlt : x < -(π/2) := lt_of_le_of_ne hmem.2 hx
    rw [← sfun_even, sfun_neg (by linarith) (by linarith [hmem.1])]
  have e2 : ∫ u in (-(π/2))..(π/2), sfun u = ∫ u in (-(π/2))..(π/2), (1:ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne (π/2)] with x hx hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have hlt : x < π/2 := lt_of_le_of_ne hmem.2 hx
    rw [sfun_pos hmem.1 hlt]
  have e3 : ∫ u in (π/2)..π, sfun u = ∫ u in (π/2)..π, (-1:ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne (π/2)] with x hx hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    rw [sfun_neg hmem.1 (by linarith [hmem.2])]
  rw [e1, e2, e3]; simp; ring

/-- shift-and-periodicity for convolution against sfun -/
lemma conv_shift (g : ℝ → ℝ) (hg : Function.Periodic g (2 * π)) (θ : ℝ) :
    ∫ t in (-π)..π, g t * sfun (θ - t) = ∫ u in (-π)..π, g (θ - u) * sfun u := by
  have h1 := intervalIntegral.integral_comp_sub_left (a := -π) (b := π)
    (fun u => g (θ - u) * sfun u) θ
  simp only [sub_sub_cancel] at h1
  rw [h1]
  have hper : Function.Periodic (fun u => g (θ - u) * sfun u) (2 * π) := by
    intro u
    simp only
    rw [sfun_periodic u, show θ - (u + 2 * π) = (θ - u) - 2 * π by ring, hg.sub_eq]
  have := hper.intervalIntegral_add_eq (θ - π) (-π)
  rw [show θ - π + 2 * π = θ + π by ring, show -π + 2 * π = π by ring] at this
  rw [show θ - -π = θ + π by ring, this]

lemma conv_cos (k : ℕ) (hk : k ≠ 0) (θ : ℝ) :
    ∫ t in (-π)..π, Real.cos (k * t) * sfun (θ - t) =
      4 * Real.sin (k * π / 2) / k * Real.cos (k * θ) := by
  have hg : Function.Periodic (fun t => Real.cos (k * t)) (2 * π) := by
    intro t; simp only
    rw [show (k:ℝ) * (t + 2 * π) = k * t + (k : ℕ) * (2 * π) by ring, Real.cos_add_nat_mul_two_pi]
  rw [conv_shift _ hg θ]
  have e : ∀ u, Real.cos (k * (θ - u)) * sfun u =
      Real.cos (k * θ) * (Real.cos (k * u) * sfun u) + Real.sin (k * θ) * (Real.sin (k * u) * sfun u) := by
    intro u; rw [mul_sub, Real.cos_sub]; ring
  simp only [e]
  rw [intervalIntegral.integral_add ((intInt_cos_sfun _ _ _).const_mul _)
    ((intInt_sin_sfun _ _ _).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, int_cos_sfun k hk, int_sin_sfun k]
  ring

lemma conv_const (θ : ℝ) : ∫ t in (-π)..π, sfun (θ - t) = 0 := by
  have hg : Function.Periodic (fun _ : ℝ => (1:ℝ)) (2 * π) := fun _ => rfl
  have := conv_shift _ hg θ
  simp only [one_mul] at this
  rw [this, int_sfun]


/-! ### Fejér kernel -/

def fa (M k : ℕ) : ℝ := if k = 0 then (M : ℝ) else 2 * ((M : ℝ) - k)
def fdel (k : ℕ) : ℝ := if k = 0 then 1 else 2

def Fej (M : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range (M+1), fa M k * Real.cos (k * t)
def Dir (M : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range (M+1), fdel k * Real.cos (k * t)

lemma fej_succ (M : ℕ) (t : ℝ) : Fej (M+1) t = Fej M t + Dir M t := by
  unfold Fej Dir
  rw [Finset.sum_range_succ (fun k => fa (M+1) k * Real.cos (k * t)) (M+1)]
  have : fa (M+1) (M+1) = 0 := by simp [fa]
  rw [this, zero_mul, add_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold fa fdel; split_ifs <;> push_cast <;> ring

lemma dir_id (M : ℕ) (t : ℝ) :
    (1 - Real.cos t) * Dir M t = Real.cos (M * t) - Real.cos ((M+1 : ℕ) * t) := by
  induction M with
  | zero => norm_num [Dir, fdel]
  | succ M ih =>
    unfold Dir at ih ⊢
    rw [Finset.sum_range_succ, mul_add, ih]
    have : fdel (M+1) = 2 := by simp [fdel]
    rw [this]
    have e1 : ((M + 1 + 1 : ℕ) : ℝ) * t = ((M+1 : ℕ) : ℝ) * t + t := by push_cast; ring
    have e2 : (M : ℝ) * t = ((M+1 : ℕ) : ℝ) * t - t := by push_cast; ring
    rw [e1, e2, Real.cos_add, Real.cos_sub]
    push_cast; ring

lemma fej_id (M : ℕ) (t : ℝ) : (1 - Real.cos t) * Fej M t = 1 - Real.cos (M * t) := by
  induction M with
  | zero => simp [Fej, fa]
  | succ M ih =>
    rw [fej_succ, mul_add, ih, dir_id]; push_cast; ring

lemma fej_at (M : ℕ) (t : ℝ) (h : ∀ k : ℕ, Real.cos (k * t) = 1) : Fej M t = (M : ℝ)^2 := by
  induction M with
  | zero => simp [Fej, fa]
  | succ M ih =>
    rw [fej_succ, ih]
    have hD : Dir M t = 1 + 2 * M := by
      unfold Dir
      simp only [h, mul_one]
      rw [Finset.sum_range_succ']
      simp only [fdel, Nat.succ_ne_zero, if_false, if_true, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      ring
    rw [hD]; push_cast; ring

/-- the ratio appearing in the Jackson kernel -/
def ratio (M : ℕ) (t : ℝ) : ℝ :=
  if Real.sin (t/2) = 0 then (M : ℝ) else Real.sin (M*t/2) / Real.sin (t/2)

lemma ratio_sq (M : ℕ) (t : ℝ) : ratio M t ^ 2 = Fej M t := by
  unfold ratio
  split_ifs with h
  · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    have ht : t = 2 * (n * π) := by linarith
    rw [fej_at M t (fun k => by
      rw [show (k : ℝ) * t = ((k * n : ℤ) : ℝ) * (2 * π) by rw [ht]; push_cast; ring]
      exact Real.cos_int_mul_two_pi _)]
  · have h1 := fej_id M t
    have hc : 1 - Real.cos t = 2 * Real.sin (t/2) ^ 2 := by
      have := Real.cos_two_mul (t / 2)
      rw [show 2 * (t / 2) = t by ring] at this
      nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
    have hcM : 1 - Real.cos (M * t) = 2 * Real.sin (M * t / 2) ^ 2 := by
      have := Real.cos_two_mul (M * t / 2)
      rw [show 2 * (M * t / 2) = M * t by ring] at this
      nlinarith [Real.sin_sq_add_cos_sq (M * t / 2)]
    rw [hc, hcM] at h1
    have hs : Real.sin (t/2) ^ 2 ≠ 0 := pow_ne_zero 2 h
    rw [div_pow]
    field_simp
    nlinarith [h1]


/-! ### cosine polynomials -/

def cosv (N : ℕ) (j : Fin (N+1)) : ℝ → ℝ := fun t => Real.cos ((j : ℕ) * t)
def cosSpan (N : ℕ) : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ (Set.range (cosv N))

lemma cos_mem {N k : ℕ} (hk : k ≤ N) : (fun t : ℝ => Real.cos (k * t)) ∈ cosSpan N :=
  Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩

lemma cos_mul_mem {n m i j : ℕ} (hi : i ≤ n) (hj : j ≤ m) :
    (fun t : ℝ => Real.cos (i * t) * Real.cos (j * t)) ∈ cosSpan (n + m) := by
  have e : (fun t : ℝ => Real.cos (i * t) * Real.cos (j * t)) =
      (1/2 : ℝ) • ((fun t : ℝ => Real.cos (((i + j : ℕ) : ℝ) * t)) +
        (fun t : ℝ => Real.cos (((if j ≤ i then i - j else j - i : ℕ) : ℝ) * t))) := by
    funext t
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [cos_mul_cos']
    congr 2
    split_ifs with h
    · push_cast [h]; ring_nf
    · push_cast [le_of_lt (not_le.mp h)]
      rw [show ((i:ℝ) - j) * t = -(((j:ℝ) - i) * t) by ring, Real.cos_neg]; ring
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ (cos_mem (by omega)) (cos_mem ?_))
  split_ifs <;> omega

lemma mul_mem' {n m : ℕ} {f g : ℝ → ℝ} (hf : f ∈ cosSpan n) (hg : g ∈ cosSpan m) :
    f * g ∈ cosSpan (n + m) := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hg
  rw [Finset.sum_mul]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  have : a i • cosv n i * c j • cosv m j = (a i * c j) •
      (fun t : ℝ => Real.cos (((i : ℕ) : ℝ) * t) * Real.cos (((j : ℕ) : ℝ) * t)) := by
    funext t; simp [cosv]; ring
  rw [this]
  exact Submodule.smul_mem _ _ (cos_mul_mem (by omega) (by omega))

lemma fej_mem (M : ℕ) (hM : 1 ≤ M) : Fej M ∈ cosSpan (M - 1) := by
  have : Fej M = ∑ k ∈ Finset.range (M+1), fa M k • (fun t : ℝ => Real.cos (k * t)) := by
    funext t; simp [Fej, Finset.sum_apply]
  rw [this]
  refine Submodule.sum_mem _ (fun k hk => ?_)
  by_cases h : k ≤ M - 1
  · exact Submodule.smul_mem _ _ (cos_mem h)
  · have : k = M := by simp at hk; omega
    subst this
    have : fa k k = 0 := by simp [fa]
    rw [this, zero_smul]; exact Submodule.zero_mem _


/-! ### Jackson kernel expansion -/

def kap (M : ℕ) : ℝ := 3 / (2 * Real.pi * M * (2 * (M : ℝ)^2 + 1))

lemma jackson_eq (M : ℕ) (t : ℝ) : jackson M t = kap M * Fej M t ^ 2 := by
  unfold jackson kap
  rw [← ratio_sq]
  unfold ratio
  ring

lemma jackson_mem (M : ℕ) (hM : 1 ≤ M) : jackson M ∈ cosSpan (2 * M - 2) := by
  have h := mul_mem' (fej_mem M hM) (fej_mem M hM)
  have e : jackson M = kap M • (Fej M * Fej M) := by
    funext t; simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, jackson_eq]; ring
  rw [e, show 2 * M - 2 = (M - 1) + (M - 1) by omega]
  exact Submodule.smul_mem _ _ h

lemma jackson_expand (M : ℕ) (hM : 1 ≤ M) :
    ∃ b : ℕ → ℝ, (∀ k, 2 * M - 2 < k → b k = 0) ∧
      ∀ t, jackson M t = ∑ k ∈ Finset.range (2 * M - 1), b k * Real.cos (k * t) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (jackson_mem M hM)
  refine ⟨fun k => if h : k < 2 * M - 2 + 1 then c ⟨k, h⟩ else 0, fun k hk => by
    simp only; rw [dif_neg (by omega)], fun t => ?_⟩
  rw [← hc, show 2 * M - 1 = 2 * M - 2 + 1 by omega, Finset.sum_apply,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.smul_apply, cosv, smul_eq_mul]
  rw [dif_pos j.2]

lemma intInt_J (M : ℕ) (hM : 1 ≤ M) (f : ℝ → ℝ) (hf : ∀ k : ℕ, IntervalIntegrable
    (fun t => Real.cos (k * t) * f t) volume (-π) π) :
    IntervalIntegrable (fun t => jackson M t * f t) volume (-π) π := by
  obtain ⟨b, -, hb⟩ := jackson_expand M hM
  have : (fun t => jackson M t * f t) =
      fun t => ∑ k ∈ Finset.range (2 * M - 1), b k * (Real.cos (k * t) * f t) := by
    funext t; rw [hb, Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [this]
  have key : ∀ S : Finset ℕ, IntervalIntegrable
      (fun t => ∑ k ∈ S, b k * (Real.cos (k * t) * f t)) volume (-π) π := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert k S hk ih =>
      simp only [Finset.sum_insert hk]
      exact ((hf k).const_mul (b k)).add ih
  exact key _

lemma int_J_cos (M : ℕ) (hM : 1 ≤ M) (b : ℕ → ℝ) (hb0 : ∀ k, 2 * M - 2 < k → b k = 0)
    (hb : ∀ t, jackson M t = ∑ k ∈ Finset.range (2 * M - 1), b k * Real.cos (k * t))
    (l : ℕ) (hl : l ≠ 0) :
    ∫ t in (-π)..π, jackson M t * Real.cos (l * t) = π * b l := by
  simp only [hb, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by
    simpa [mul_assoc] using ((intInt_cos (k:ℝ) (-π) π).mul_continuousOn
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).const_mul (b k))]
  simp only [mul_assoc, intervalIntegral.integral_const_mul, orth]
  by_cases h : l < 2 * M - 1
  · rw [Finset.sum_eq_single l]
    · simp [hl]; ring
    · intro k _ hk; simp [hk]
    · intro h'; exact absurd (Finset.mem_range.mpr h) h'
  · rw [hb0 l (by omega), mul_zero]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have : k ≠ l := by simp at hk; omega
    simp [this]

lemma conv_J (M : ℕ) (hM : 1 ≤ M) (b : ℕ → ℝ)
    (hb : ∀ t, jackson M t = ∑ k ∈ Finset.range (2 * M - 1), b k * Real.cos (k * t)) (θ : ℝ) :
    ∫ t in (-π)..π, jackson M t * sfun (θ - t) =
      ∑ k ∈ Finset.range (2 * M - 1),
        (if k = 0 then 0 else b k * (4 * Real.sin (k * π / 2) / k * Real.cos (k * θ))) := by
  have hint : ∀ k : ℕ, IntervalIntegrable (fun t => Real.cos (k * t) * sfun (θ - t)) volume (-π) π :=
    fun k => bdd_intInt ((by fun_prop : Continuous fun t => Real.cos ((k:ℝ) * t)).measurable.mul
      (sfun_measurable.comp (measurable_const.sub measurable_id))) (C := 1) (fun x => by
        show |Real.cos (k * x) * sfun (θ - x)| ≤ 1
        rw [abs_mul]; exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (abs_sfun_le _)) _ _
  simp only [hb, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by
    simpa [mul_assoc] using (hint k).const_mul (b k))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  split_ifs with hk
  · subst hk
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, one_mul]
    rw [conv_const, mul_zero]
  · rw [conv_cos k hk]


lemma D_cos (K : ℕ) (hK : 2 ≤ K) (θ : ℝ) :
    (jacksonDerivative K).eval (Real.cos θ) =
      ∫ t in (-π)..π, jackson (K/2+1) t * sfun (θ - t) := by
  have hM : 1 ≤ K/2+1 := by omega
  obtain ⟨b, hb0, hb⟩ := jackson_expand (K/2+1) hM
  rw [conv_J _ hM b hb θ]
  set g : ℕ → ℝ := fun k => if k = 0 then 0 else b k * (4 * Real.sin (k * π / 2) / k * Real.cos (k * θ))
    with hg
  have hN : 2 * (K/2+1) - 1 = 2 * (K/2) + 1 := by omega
  have hgz : ∀ l, 2 * (K/2) < l → g l = 0 := fun l hl => by
    simp only [hg]; split_ifs
    · rfl
    · rw [hb0 l (by omega), zero_mul]
  have lhs : (jacksonDerivative K).eval (Real.cos θ) = ∑ l ∈ Finset.range K, g l := by
    unfold jacksonDerivative
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.T_real_cos]
    simp only [hg, Int.cast_natCast]
    split_ifs with hl
    · simp
    · rw [int_J_cos _ hM b hb0 hb l hl]
      have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl
      have hp := Real.pi_pos.ne'
      rw [show Real.pi * l / 2 = l * Real.pi / 2 by ring]
      field_simp
  rw [lhs, hN]
  have h1 : ∑ l ∈ Finset.range K, g l = ∑ l ∈ Finset.range (K+1), g l := by
    rw [Finset.sum_range_succ]
    have : g K = 0 := by
      by_cases hk : 2 * (K/2) < K
      · exact hgz K hk
      · have hKe : K = 2 * (K/2) := by omega
        simp only [hg]; split_ifs
        · rfl
        · have : Real.sin (K * π / 2) = 0 := by
            rw [show (K:ℝ) * π / 2 = ((K/2 : ℕ) : ℝ) * π by
              rw [show ((K/2 : ℕ) : ℝ) = (K:ℝ)/2 by
                rw [Nat.cast_div (by omega) (by norm_num)]; norm_num]
              ring]
            exact Real.sin_nat_mul_pi _
          rw [this]; simp
    rw [this, add_zero]
  have h2 : ∑ l ∈ Finset.range (2 * (K/2) + 1), g l = ∑ l ∈ Finset.range (K+1), g l := by
    apply Finset.sum_subset
    · intro x hx; simp at hx ⊢; omega
    · intro x _ hx; simp at hx; exact hgz x (by omega)
  rw [h1, h2]


/-! ### normalization -/

lemma sum_sq_range (M : ℕ) : ∑ j ∈ Finset.range M, ((j : ℝ))^2 = (M - 1) * M * (2 * M - 1) / 6 := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma intInt_coscos (k l : ℕ) : IntervalIntegrable (fun t => Real.cos (k * t) * Real.cos (l * t)) volume (-π) π :=
  (by fun_prop : Continuous fun t => Real.cos ((k:ℝ) * t) * Real.cos ((l:ℝ) * t)).intervalIntegrable _ _

lemma int_fej_sq (M : ℕ) : ∫ t in (-π)..π, Fej M t ^ 2 = 2 * π * M * (2 * M^2 + 1) / 3 := by
  have e : ∀ t, Fej M t ^ 2 = ∑ k ∈ Finset.range (M+1), ∑ l ∈ Finset.range (M+1),
      fa M k * fa M l * (Real.cos (k * t) * Real.cos (l * t)) := by
    intro t; rw [sq, Fej, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  simp only [e]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by
    have key : ∀ S : Finset ℕ, IntervalIntegrable (fun t => ∑ l ∈ S,
        fa M k * fa M l * (Real.cos (k * t) * Real.cos (l * t))) volume (-π) π := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert l S hl ih =>
        simp only [Finset.sum_insert hl]
        exact ((intInt_coscos k l).const_mul _).add ih
    exact key _)]
  have inner : ∀ k ∈ Finset.range (M+1), ∫ t in (-π)..π, ∑ l ∈ Finset.range (M+1),
      fa M k * fa M l * (Real.cos (k * t) * Real.cos (l * t)) =
      fa M k ^ 2 * (if k = 0 then 2 * π else π) := by
    intro k hk
    rw [intervalIntegral.integral_finsetSum (fun l _ => (intInt_coscos k l).const_mul _)]
    simp only [intervalIntegral.integral_const_mul, orth]
    rw [Finset.sum_eq_single k]
    · simp only [if_true]; ring
    · intro l _ hl; simp [Ne.symm hl]
    · intro h; exact absurd hk h
  rw [Finset.sum_congr rfl inner, Finset.sum_range_succ']
  simp only [Nat.succ_ne_zero, if_false, if_true]
  have h2 : ∑ k ∈ Finset.range M, fa M (k+1) ^ 2 * π =
      4 * π * ∑ j ∈ Finset.range M, ((j : ℝ))^2 := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp at hj
    simp only [fa, Nat.succ_ne_zero, if_false]
    rw [show M - 1 - j + 1 = M - j by omega, Nat.cast_sub (by omega)]; ring
  rw [h2, sum_sq_range]
  simp [fa]; ring

lemma int_jackson (M : ℕ) (hM : 1 ≤ M) : ∫ t in (-π)..π, jackson M t = 1 := by
  simp only [jackson_eq]
  rw [intervalIntegral.integral_const_mul, int_fej_sq, kap]
  have hp := Real.pi_pos
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  field_simp

lemma kap_nonneg (M : ℕ) : 0 ≤ kap M := by unfold kap; positivity

lemma jackson_nonneg (M : ℕ) (t : ℝ) : 0 ≤ jackson M t := by
  rw [jackson_eq]; exact mul_nonneg (kap_nonneg M) (sq_nonneg _)

lemma intInt_jackson (M : ℕ) (hM : 1 ≤ M) (a b : ℝ) :
    IntervalIntegrable (jackson M) volume a b := by
  obtain ⟨b', -, hb⟩ := jackson_expand M hM
  have : jackson M = fun t => ∑ k ∈ Finset.range (2 * M - 1), b' k * Real.cos (k * t) := funext hb
  rw [this]
  exact (by fun_prop : Continuous fun t => ∑ k ∈ Finset.range (2 * M - 1), b' k * Real.cos ((k:ℝ) * t)).intervalIntegrable _ _


/-! ### tail bounds -/

lemma jackson_even (M : ℕ) (t : ℝ) : jackson M (-t) = jackson M t := by
  simp only [jackson_eq, Fej]
  congr 2
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mul_neg, Real.cos_neg]

lemma jackson_pt (M : ℕ) (hM : 1 ≤ M) {t : ℝ} (ht0 : 0 < t) (htp : t ≤ π) :
    jackson M t ≤ 24 / ((M : ℝ)^3 * t^4) := by
  have hp := Real.pi_pos
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hs : 0 < Real.sin (t/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsl : t / π ≤ Real.sin (t/2) := by
    have := Real.mul_le_sin (x := t/2) (by linarith) (by linarith)
    calc t / π = 2 / π * (t/2) := by ring
      _ ≤ _ := this
  have hr : |ratio M t| ≤ 1 / Real.sin (t/2) := by
    unfold ratio; rw [if_neg hs.ne', abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hs.le
  have hr4 : ratio M t ^ 4 ≤ (π / t)^4 := by
    have h1 : |ratio M t| ≤ π / t := by
      refine hr.trans ?_
      rw [div_le_div_iff₀ hs (by positivity)]
      rw [div_le_iff₀ hp] at hsl; linarith
    calc ratio M t ^ 4 = |ratio M t| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ ≤ (π/t)^4 := pow_le_pow_left₀ (abs_nonneg _) h1 4
  have hk : kap M ≤ 3 / (4 * π * (M:ℝ)^3) := by
    unfold kap
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [hp, hMr]
  have hJ : jackson M t = kap M * ratio M t ^ 4 := by
    rw [jackson_eq, ← ratio_sq]; ring
  rw [hJ]
  have hpi3 : π^3 < 32 := by
    have h := Real.pi_lt_d2
    have h' : π < 3.15 := h
    have h2 : π^2 < 3.15^2 := by nlinarith
    have h3 : π^3 < 3.15^3 := by nlinarith
    norm_num at h3; linarith
  calc kap M * ratio M t ^ 4 ≤ 3 / (4 * π * (M:ℝ)^3) * (π/t)^4 :=
        mul_le_mul hk hr4 (by positivity) (by positivity)
    _ = 3 * π^3 / (4 * (M:ℝ)^3 * t^4) := by field_simp
    _ ≤ 24 / ((M : ℝ)^3 * t^4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 < (M:ℝ)^3 * t^4 := by positivity
        nlinarith

lemma tail (M : ℕ) (hM : 1 ≤ M) {u : ℝ} (hu : 0 < u) (hup : u ≤ π) :
    ∫ t in u..π, jackson M t ≤ 8 / ((M:ℝ) * u)^3 := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hcont : ContinuousOn (fun t : ℝ => 24 / ((M:ℝ)^3) * t ^ (-4 : ℤ)) (Set.uIcc u π) := by
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.zpow₀ continuousOn_id _ (fun x hx => Or.inl ?_)
    rw [Set.uIcc_of_le hup] at hx; exact (lt_of_lt_of_le hu hx.1).ne'
  calc ∫ t in u..π, jackson M t ≤ ∫ t in u..π, 24 / ((M:ℝ)^3) * t ^ (-4 : ℤ) := by
        refine intervalIntegral.integral_mono_on hup (intInt_jackson M hM _ _)
          (hcont.intervalIntegrable) (fun t ht => ?_)
        have ht0 : 0 < t := lt_of_lt_of_le hu ht.1
        refine (jackson_pt M hM ht0 ht.2).trans (le_of_eq ?_)
        rw [zpow_neg, zpow_ofNat]; field_simp
    _ = 24 / ((M:ℝ)^3) * ((π ^ (-3 : ℤ) - u ^ (-3:ℤ)) / (-3)) := by
        rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, ?_⟩)]
        · norm_num
        · rw [Set.uIcc_of_le hup]; intro h; linarith [h.1]
    _ ≤ 8 / ((M:ℝ) * u)^3 := by
        have h1 : 0 < π ^ (-3:ℤ) := by positivity
        have h2 : u ^ (-3 : ℤ) = 1 / u^3 := by rw [zpow_neg, zpow_ofNat, one_div]
        rw [h2]
        have : 24 / ((M:ℝ)^3) * ((π ^ (-3 : ℤ) - 1 / u^3) / (-3)) =
            8 / ((M:ℝ) * u)^3 - 8 / (M:ℝ)^3 * π ^ (-3 : ℤ) := by
          field_simp; ring
        rw [this]
        have : 0 ≤ 8 / (M:ℝ)^3 * π ^ (-3 : ℤ) := by positivity
        linarith


/-! ### pointwise comparison with sign -/

lemma sfun_shift {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) {t : ℝ} (ht : |t| ≤ |x|) :
    sfun (Real.arccos x - t) = sfun (Real.arccos x) := by
  have hp := Real.pi_pos
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  have hab := Real.arcsin_le_pi_div_two x
  have hab' := Real.neg_pi_div_two_le_arcsin x
  rw [abs_le] at ht
  rcases lt_trichotomy x 0 with h | rfl | h
  · have hy : Real.arcsin x < 0 := Real.arcsin_lt_zero.mpr h
    have hlt : Real.arcsin x < x := by
      have := Real.sin_lt (x := -Real.arcsin x) (by linarith)
      rw [Real.sin_neg, Real.sin_arcsin hx1 hx2] at this; linarith
    rw [abs_of_neg h] at ht
    rw [sfun_neg (by linarith) (by linarith), sfun_neg (by linarith) (by linarith)]
  · simp at ht; have : t = 0 := by linarith [ht.1, ht.2]
    subst this; simp
  · have hy : 0 < Real.arcsin x := Real.arcsin_pos.mpr h
    have hlt : x < Real.arcsin x := by
      have := Real.sin_lt hy
      rw [Real.sin_arcsin hx1 hx2] at this; linarith
    rw [abs_of_pos h] at ht
    rw [sfun_pos (by linarith) (by linarith), sfun_pos (by linarith) (by linarith)]

def Dpoly (K : ℕ) : Polynomial ℝ := jacksonDerivative K

lemma D_eq_conv (K : ℕ) (hK : 2 ≤ K) {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    (jacksonDerivative K).eval x =
      ∫ t in (-π)..π, jackson (K/2+1) t * sfun (Real.arccos x - t) := by
  rw [← D_cos K hK, Real.cos_arccos hx1 hx2]

lemma sign_eq_sfun {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) : sign x = sfun (Real.arccos x) := by
  simp [sfun, Real.cos_arccos hx1 hx2]

lemma jackson_bdd (M : ℕ) (hM : 1 ≤ M) : ∃ C, ∀ t, |jackson M t| ≤ C := by
  obtain ⟨b, -, hb⟩ := jackson_expand M hM
  refine ⟨∑ k ∈ Finset.range (2 * M - 1), |b k|, fun t => ?_⟩
  rw [hb]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

lemma jackson_meas (M : ℕ) (hM : 1 ≤ M) : Measurable (jackson M) := by
  obtain ⟨b, -, hb⟩ := jackson_expand M hM
  have : jackson M = fun t => ∑ k ∈ Finset.range (2 * M - 1), b k * Real.cos (k * t) := funext hb
  rw [this]; fun_prop

lemma intInt_Jsf (M : ℕ) (hM : 1 ≤ M) (θ : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t => jackson M t * sfun (θ - t)) volume a b := by
  obtain ⟨C, hC⟩ := jackson_bdd M hM
  exact bdd_intInt ((jackson_meas M hM).mul (sfun_measurable.comp (measurable_const.sub measurable_id)))
    (C := C) (fun t => by
      show |jackson M t * sfun (θ - t)| ≤ C
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_sfun_le _) |>.trans (hC t)) a b


lemma D_abs_le (K : ℕ) (hK : 2 ≤ K) {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |(jacksonDerivative K).eval x| ≤ 1 := by
  have hM : 1 ≤ K/2+1 := by omega
  rw [D_eq_conv K hK hx1 hx2]
  have hp := Real.pi_pos
  refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
  rw [← int_jackson (K/2+1) hM]
  refine intervalIntegral.integral_mono_on (by linarith) (intInt_Jsf _ hM _ _ _).abs
    (intInt_jackson _ hM _ _) (fun t _ => ?_)
  rw [abs_mul, abs_of_nonneg (jackson_nonneg _ _)]
  exact mul_le_of_le_one_right (jackson_nonneg _ _) (abs_sfun_le _)

lemma piece_le (M : ℕ) (hM : 1 ≤ M) (θ c : ℝ) {a b : ℝ} (hab : a ≤ b) (hc : |c| ≤ 1) :
    |∫ t in a..b, (jackson M t * sfun (θ - t) - c * jackson M t)| ≤ 2 * ∫ t in a..b, jackson M t := by
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab
    ((intInt_Jsf M hM θ a b).sub ((intInt_jackson M hM a b).const_mul c)).abs
    ((intInt_jackson M hM a b).const_mul 2) (fun t _ => ?_)
  have hJ := jackson_nonneg M t
  rw [show jackson M t * sfun (θ - t) - c * jackson M t = jackson M t * (sfun (θ - t) - c) by ring,
    abs_mul, abs_of_nonneg hJ]
  have : |sfun (θ - t) - c| ≤ 2 := (abs_sub _ _).trans (by linarith [abs_sfun_le (θ - t)])
  nlinarith

lemma D_sign_le (K : ℕ) (hK : 2 ≤ K) {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) (hx : x ≠ 0) :
    |(jacksonDerivative K).eval x - sign x| ≤ 32 / (((K/2+1 : ℕ) : ℝ) * |x|)^3 := by
  set M := K/2+1 with hMdef
  have hM : 1 ≤ M := by omega
  have hp := Real.pi_pos
  set θ := Real.arccos x
  set u := |x| with hu
  have hu0 : 0 < u := abs_pos.mpr hx
  have hu1 : u ≤ 1 := abs_le.mpr ⟨hx1, hx2⟩
  have hupi : u < π := by linarith [Real.pi_gt_three]
  have hc : |sfun θ| ≤ 1 := abs_sfun_le _
  have e : (jacksonDerivative K).eval x - sign x =
      ∫ t in (-π)..π, (jackson M t * sfun (θ - t) - sfun θ * jackson M t) := by
    rw [intervalIntegral.integral_sub (intInt_Jsf M hM θ _ _) ((intInt_jackson M hM _ _).const_mul _),
      intervalIntegral.integral_const_mul, int_jackson M hM, mul_one, D_eq_conv K hK hx1 hx2,
      sign_eq_sfun hx1 hx2]
  have hI : ∀ a b, IntervalIntegrable (fun t => jackson M t * sfun (θ - t) - sfun θ * jackson M t)
      volume a b := fun a b => (intInt_Jsf M hM θ a b).sub ((intInt_jackson M hM a b).const_mul _)
  rw [e, ← intervalIntegral.integral_add_adjacent_intervals (b := -u) (hI _ _) (hI _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := -u) (b := u) (hI _ _) (hI _ _)]
  have hmid : ∫ t in (-u)..u, (jackson M t * sfun (θ - t) - sfun θ * jackson M t) = 0 := by
    rw [← intervalIntegral.integral_zero (a := -u) (b := u) (μ := volume)]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by linarith)] at ht
    rw [sfun_shift hx1 hx2 (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)]; ring
  rw [hmid, zero_add]
  have hL := piece_le M hM θ (sfun θ) (a := -π) (b := -u) (by linarith) hc
  have hR := piece_le M hM θ (sfun θ) (a := u) (b := π) (by linarith) hc
  have heven : ∫ t in (-π)..(-u), jackson M t = ∫ t in u..π, jackson M t := by
    have := intervalIntegral.integral_comp_neg (a := u) (b := π) (jackson M)
    simp only [jackson_even] at this
    exact this.symm
  have ht := tail M hM hu0 hupi.le
  rw [heven] at hL
  calc _ ≤ |∫ t in (-π)..(-u), (jackson M t * sfun (θ - t) - sfun θ * jackson M t)| +
        |∫ t in u..π, (jackson M t * sfun (θ - t) - sfun θ * jackson M t)| := abs_add_le _ _
    _ ≤ 2 * (8 / ((M:ℝ) * u)^3) + 2 * (8 / ((M:ℝ) * u)^3) := by linarith
    _ = 32 / ((M:ℝ) * u)^3 := by ring


/-! ### polynomial facts -/

lemma q_derivative (K : ℕ) : (q K).derivative = jacksonDerivative K := by
  unfold q
  rw [Polynomial.derivative_sum]
  conv_rhs => rw [(jacksonDerivative K).as_sum_support_C_mul_X_pow]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.derivative_C_mul_X_pow]
  simp only [Nat.add_sub_cancel]
  congr 1
  push_cast
  field_simp

lemma q_eval_zero (K : ℕ) : (q K).eval 0 = 0 := by
  simp [q, Polynomial.eval_finsetSum]

lemma D_natDegree (K : ℕ) : (jacksonDerivative K).natDegree ≤ K - 1 := by
  unfold jacksonDerivative
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun l hl => ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.Chebyshev.natDegree_T]
  simp at hl; simp; omega

lemma q_natDegree (K : ℕ) (hK : 1 ≤ K) : (q K).natDegree ≤ K := by
  unfold q
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  have := Polynomial.le_natDegree_of_mem_supp j hj
  have := D_natDegree K
  omega

lemma q_ftc (K : ℕ) (x : ℝ) : (q K).eval x = ∫ t in (0:ℝ)..x, (jacksonDerivative K).eval t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => (q K).eval t)
    (fun t _ => by rw [← q_derivative]; exact Polynomial.hasDerivAt (q K) t)
    ((Polynomial.continuous _).intervalIntegrable _ _), q_eval_zero, sub_zero]

lemma D_odd (K : ℕ) (x : ℝ) : (jacksonDerivative K).eval (-x) = -(jacksonDerivative K).eval x := by
  unfold jacksonDerivative
  rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.Chebyshev.T_eval_neg]
  split_ifs with h0
  · simp
  · rcases Nat.even_or_odd l with ⟨m, hm⟩ | ho
    · have : Real.sin (Real.pi * l / 2) = 0 := by
        rw [show Real.pi * l / 2 = (m : ℕ) * Real.pi by rw [hm]; push_cast; ring]
        exact Real.sin_nat_mul_pi m
      simp [this]
    · rw [Int.negOnePow_odd _ (by exact_mod_cast ho.natCast)]
      simp

lemma q_even (K : ℕ) (x : ℝ) : (q K).eval (-x) = (q K).eval x := by
  rw [q_ftc, q_ftc]
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x)
    (fun t => (jacksonDerivative K).eval t)
  simp only [D_odd, intervalIntegral.integral_neg, neg_zero] at h
  have h2 := intervalIntegral.integral_symm (μ := volume) (f := fun t => (jacksonDerivative K).eval t) 0 (-x)
  linarith


/-! ### scalar estimates -/

lemma sign_neg (x : ℝ) : sign (-x) = -sign x := by
  unfold sign
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [h, not_lt.mpr (neg_nonneg.mpr h.le), (neg_pos.mpr h).ne', h.not_gt]
  · simp
  · simp [h, not_lt.mpr h.le, h.ne']

lemma sign_intInt (a b : ℝ) : IntervalIntegrable sign volume a b :=
  sign_monotone.intervalIntegrable

lemma int_sign (x : ℝ) : ∫ t in (0:ℝ)..x, sign t = |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx (f := fun t => t)
      continuousOn_id (fun t ht => ?_) (sign_intInt 0 x)]
    · simp [abs_of_nonneg hx]
    · have : sign t = 1 := by unfold sign; simp [not_lt.mpr ht.1.le, ht.1.ne']
      rw [this]; exact hasDerivAt_id t
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.le
      (f := fun t => -t) continuousOn_neg (fun t ht => ?_) (sign_intInt x 0)]
    · simp [abs_of_neg hx]
    · have : sign t = -1 := by unfold sign; simp [ht.2]
      rw [this]; exact (hasDerivAt_id t).neg

def Efun (K : ℕ) (x : ℝ) : ℝ := |(jacksonDerivative K).eval x - sign x|

lemma Efun_intInt (K : ℕ) (a b : ℝ) : IntervalIntegrable (Efun K) volume a b :=
  (((Polynomial.continuous _).intervalIntegrable a b).sub (sign_intInt a b)).abs

lemma Efun_even (K : ℕ) (x : ℝ) : Efun K (-x) = Efun K x := by
  unfold Efun; rw [D_odd, sign_neg, ← abs_neg]; ring_nf

lemma Efun_le2 (K : ℕ) (hK : 2 ≤ K) {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) : Efun K x ≤ 2 := by
  unfold Efun
  have := D_abs_le K hK hx1 hx2
  have := abs_sign_le x
  calc _ ≤ |(jacksonDerivative K).eval x| + |sign x| := abs_sub _ _
    _ ≤ 2 := by linarith

lemma Mr_facts (K : ℕ) (hK : 2 ≤ K) :
    (1 : ℝ) ≤ ((K/2+1 : ℕ) : ℝ) ∧ (K : ℝ) ≤ 2 * ((K/2+1 : ℕ) : ℝ) := by
  constructor
  · exact_mod_cast (by omega : 1 ≤ K/2+1)
  · exact_mod_cast (by omega : K ≤ 2 * (K/2+1))

lemma int_Efun_half (K : ℕ) (hK : 2 ≤ K) :
    ∫ x in (0:ℝ)..1, Efun K x ≤ 8 / ((K/2+1 : ℕ) : ℝ) := by
  obtain ⟨hM1, -⟩ := Mr_facts K hK
  set Mr := ((K/2+1 : ℕ) : ℝ)
  have hMpos : 0 < Mr := by linarith
  by_cases ha : 1 ≤ 2 / Mr
  · calc ∫ x in (0:ℝ)..1, Efun K x ≤ ∫ x in (0:ℝ)..1, (2:ℝ) := by
          refine intervalIntegral.integral_mono_on (by norm_num) (Efun_intInt K _ _)
            intervalIntegrable_const (fun x hx => Efun_le2 K hK (by linarith [hx.1]) hx.2)
      _ = 2 := by simp
      _ ≤ 8 / Mr := by
          rw [le_div_iff₀ hMpos]; rw [le_div_iff₀ hMpos] at ha; linarith
  · push Not at ha
    set a := 2 / Mr with hadef
    have ha0 : 0 < a := by positivity
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := a) (Efun_intInt K _ _)
      (Efun_intInt K _ _)]
    have h1 : ∫ x in (0:ℝ)..a, Efun K x ≤ 2 * a := by
      calc ∫ x in (0:ℝ)..a, Efun K x ≤ ∫ x in (0:ℝ)..a, (2:ℝ) := by
            refine intervalIntegral.integral_mono_on ha0.le (Efun_intInt K _ _)
              intervalIntegrable_const (fun x hx => Efun_le2 K hK (by linarith [hx.1]) (by linarith [hx.2]))
        _ = 2 * a := by simp; ring
    have hcont : ContinuousOn (fun x : ℝ => 32 / Mr^3 * x ^ (-3 : ℤ)) (Set.uIcc a 1) := by
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.zpow₀ continuousOn_id _ (fun x hx => Or.inl ?_)
      rw [Set.uIcc_of_le ha.le] at hx; exact (lt_of_lt_of_le ha0 hx.1).ne'
    have h2 : ∫ x in a..1, Efun K x ≤ 16 / (Mr^3 * a^2) := by
      calc ∫ x in a..1, Efun K x ≤ ∫ x in a..1, 32 / Mr^3 * x ^ (-3 : ℤ) := by
            refine intervalIntegral.integral_mono_on ha.le (Efun_intInt K _ _)
              hcont.intervalIntegrable (fun x hx => ?_)
            have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
            refine (D_sign_le K hK (by linarith) hx.2 hx0.ne').trans (le_of_eq ?_)
            rw [abs_of_pos hx0, zpow_neg, zpow_ofNat]; field_simp; rfl
        _ = 32 / Mr^3 * ((1 - a ^ (-2 : ℤ)) / (-2)) := by
            rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, ?_⟩)]
            · norm_num
            · rw [Set.uIcc_of_le ha.le]; intro h; linarith [h.1]
        _ ≤ 16 / (Mr^3 * a^2) := by
            rw [zpow_neg, zpow_ofNat]
            have : 32 / Mr^3 * ((1 - (a ^ 2)⁻¹) / (-2)) = 16 / (Mr^3 * a^2) - 16 / Mr^3 := by
              field_simp; ring
            rw [this]
            have : 0 ≤ 16 / Mr^3 := by positivity
            linarith
    have h3 : 16 / (Mr^3 * a^2) = 4 / Mr := by rw [hadef]; field_simp; ring
    have h4 : 2 * a = 4 / Mr := by rw [hadef]; ring
    have h5 : 4 / Mr + 4 / Mr = 8 / Mr := by ring
    linarith

lemma int_Efun_negHalf (K : ℕ) : ∫ x in (-1:ℝ)..0, Efun K x = ∫ x in (0:ℝ)..1, Efun K x := by
  have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (Efun K)
  simp only [Efun_even, neg_zero] at this
  exact this.symm


open Polynomial in
section
open Polynomial
lemma card_tuples (a m k : ℕ) (hmk : m ≤ k) :
    ((Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (k+1))).filter
      (fun r => (∑ i, r i (Finset.mem_univ i)) = m)).card = (a + m).choose m := by
  have h1 : ((Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (k+1))).filter
      (fun r => (∑ i, r i (Finset.mem_univ i)) = m)).card =
      (Finset.piAntidiag (Finset.univ : Finset (Fin (a+1))) m).card := by
    refine Finset.card_nbij' (fun r i => r i (Finset.mem_univ i)) (fun f i _ => f i) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Finset.mem_coe, Finset.mem_filter] at hr
      rw [Finset.mem_coe, Finset.mem_piAntidiag]
      exact ⟨hr.2, fun i _ => Finset.mem_univ i⟩
    · intro f hf
      rw [Finset.mem_coe, Finset.mem_piAntidiag] at hf
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_pi]
      refine ⟨fun i _ => ?_, hf.1⟩
      have h3 : f i ≤ m := calc f i ≤ Finset.univ.sum f :=
            Finset.single_le_sum (f := f) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = m := hf.1
      rw [Finset.mem_range]; show f i < k + 1; omega
    · intro r _; rfl
    · intro f _; rfl
  rw [h1, ← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ, Finset.card_univ,
    Sym.card_sym_fin_eq_multichoose, Nat.multichoose_eq]
  congr 1; omega

lemma dd_repeated (p : Polynomial ℝ) (a : ℕ) (x : ℝ) :
    (a.factorial : ℝ) * dividedDifference p a (fun _ => x) = (derivative^[a] p).eval x := by
  conv_rhs => rw [p.as_sum_support_C_mul_X_pow]
  rw [Polynomial.iterate_derivative_sum, Polynomial.eval_finsetSum, dividedDifference,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_smul,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_smul, Polynomial.eval_pow,
    Polynomial.eval_X, smul_eq_mul]
  split_ifs with hk
  · have hprod : ∀ r ∈ (Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (k+1))).filter
        (fun r => (∑ i, r i (Finset.mem_univ i)) = k - a),
        ∏ i, x ^ (r i (Finset.mem_univ i)) = x ^ (k - a) := by
      intro r hr
      rw [Finset.prod_pow_eq_pow_sum, (Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl hprod, Finset.sum_const, card_tuples a (k - a) k (by omega), nsmul_eq_mul,
      show a + (k - a) = k by omega, Nat.choose_symm hk, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]; simp

lemma sep_eval {a : ℕ} {I : Set ℝ} {f : (Fin (a+1) → ℝ) → ℝ} {M : ℝ} (h : HasSeparatedBound a I f M)
    {x : ℝ} (hx : x ∈ I) : |f (fun _ => x)| ≤ M := by
  obtain ⟨L, c, g, B, hB, hrep, hsum⟩ := h
  rw [hrep _ (fun _ => hx)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hsum)
  refine Finset.sum_le_sum (fun α _ => ?_)
  rw [abs_mul, Finset.abs_prod]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => abs_nonneg _)
    (fun i _ => (hB α i).2 x hx)) (abs_nonneg _)

lemma T_deriv_bound (l r : ℕ) (hr : 1 ≤ r) {x : ℝ} (hx : x ∈ Set.Icc (-(1/2):ℝ) (1/2)) :
    |(derivative^[r] (Polynomial.Chebyshev.T ℝ l)).eval x| ≤ (4 * (l:ℝ))^r := by
  by_cases hl : r ≤ l
  · have hB := (lemma_B_1 l r hr hl).2.1
    have h := sep_eval hB hx
    rw [← dd_repeated, abs_mul, Nat.abs_cast]
    have hf : (0:ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
    calc (r.factorial : ℝ) * |dividedDifference (Polynomial.Chebyshev.T ℝ l) r (fun _ => x)|
        ≤ r.factorial * ((4 * (l:ℝ))^r / r.factorial) := mul_le_mul_of_nonneg_left h hf.le
      _ = (4 * (l:ℝ))^r := by field_simp
  · have : derivative^[r] (Polynomial.Chebyshev.T ℝ l) = 0 := by
      apply Polynomial.iterate_derivative_eq_zero
      rw [Polynomial.Chebyshev.natDegree_T]; simp; omega
    rw [this]; simp


lemma coef_bound (K : ℕ) (hK : 2 ≤ K) (l : ℕ) (hl : l ≠ 0) :
    |4 * Real.sin (Real.pi * l / 2) / (Real.pi * l) *
      ∫ t in (-π)..π, jackson (K / 2 + 1) t * Real.cos (l*t)| ≤ 4 / l := by
  have hM : 1 ≤ K/2+1 := by omega
  have hp := Real.pi_pos
  have hl' : (0:ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl
  have hI : |∫ t in (-π)..π, jackson (K / 2 + 1) t * Real.cos (l*t)| ≤ 1 := by
    rw [← int_jackson _ hM]
    refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
    refine intervalIntegral.integral_mono_on (by linarith)
      ((intInt_J _ hM _ (fun k => (intInt_coscos k l))).abs) (intInt_jackson _ hM _ _) (fun t _ => ?_)
    rw [abs_mul, abs_of_nonneg (jackson_nonneg _ _)]
    exact mul_le_of_le_one_right (jackson_nonneg _ _) (Real.abs_cos_le_one _)
  rw [abs_mul, abs_div]
  have h4 : |(4:ℝ) * Real.sin (Real.pi * l / 2)| ≤ 4 := by
    rw [abs_mul]; nlinarith [Real.abs_sin_le_one (Real.pi * l / 2), abs_nonneg (Real.sin (Real.pi * l / 2))]
  rw [abs_of_pos (by positivity : (0:ℝ) < Real.pi * l)]
  calc |4 * Real.sin (Real.pi * l / 2)| / (Real.pi * l) * |∫ t in (-π)..π, jackson (K / 2 + 1) t * Real.cos (l*t)|
      ≤ 4 / (Real.pi * l) * 1 := by
        apply mul_le_mul (div_le_div_of_nonneg_right h4 (by positivity)) hI (abs_nonneg _) (by positivity)
    _ ≤ 4 / l := by
        rw [mul_one]; apply div_le_div_of_nonneg_left (by norm_num) hl'
        nlinarith [Real.pi_gt_three]

lemma D_deriv_bound (K : ℕ) (hK : 2 ≤ K) (r : ℕ) (hr : 1 ≤ r) {x : ℝ}
    (hx : x ∈ Set.Icc (-(1/2):ℝ) (1/2)) :
    |(derivative^[r] (jacksonDerivative K)).eval x| ≤ 4^(r+1) * (K:ℝ)^r := by
  unfold jacksonDerivative
  rw [Polynomial.iterate_derivative_sum, Polynomial.eval_finsetSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ l ∈ Finset.range K, |(derivative^[r] (Polynomial.C (if l = 0 then 0 else
      4 * Real.sin (Real.pi * l / 2) / (Real.pi * l) *
        ∫ t in (-π)..π, jackson (K / 2 + 1) t * Real.cos (l*t)) *
      Polynomial.Chebyshev.T ℝ l)).eval x| ≤ 4^(r+1) * (K:ℝ)^(r-1) := by
    intro l hl
    rw [Polynomial.iterate_derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
    split_ifs with h0
    · simp
    · have hlK : (l:ℝ) ≤ K := by exact_mod_cast (Finset.mem_range.mp hl).le
      have hl' : (0:ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero h0
      calc _ ≤ (4 / l) * (4 * (l:ℝ))^r :=
            mul_le_mul (coef_bound K hK l h0) (T_deriv_bound l r hr hx) (abs_nonneg _) (by positivity)
        _ = 4^(r+1) * (l:ℝ)^(r-1) := by
            obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
            simp only [Nat.add_sub_cancel]; field_simp; ring
        _ ≤ 4^(r+1) * (K:ℝ)^(r-1) := by gcongr
  calc _ ≤ ∑ l ∈ Finset.range K, 4^(r+1) * (K:ℝ)^(r-1) := Finset.sum_le_sum hterm
    _ = 4^(r+1) * (K:ℝ)^r := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring

end

end OTDJackson
open scoped ComplexOrder
namespace OTDUni
open Matrix OptimalTraceDistance.Estimation Polynomial

def hh (m : ℕ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ f ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) m, ∏ i, x i ^ f i

lemma inner_eq (a j : ℕ) (hj : a ≤ j) (x : Fin (a+1) → ℝ) :
    ∑ r ∈ (Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (j+1))).filter
      (fun r => (∑ i, r i (Finset.mem_univ i)) = j - a), ∏ i, x i ^ (r i (Finset.mem_univ i)) =
    hh (j - a) x := by
  unfold hh
  refine Finset.sum_nbij' (fun r i => r i (Finset.mem_univ i)) (fun f i _ => f i) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter] at hr
    rw [Finset.mem_piAntidiag]
    exact ⟨hr.2, fun i _ => Finset.mem_univ i⟩
  · intro f hf
    rw [Finset.mem_piAntidiag] at hf
    rw [Finset.mem_filter, Finset.mem_pi]
    refine ⟨fun i _ => ?_, hf.1⟩
    have h3 : f i ≤ j - a := by
      have := Finset.single_le_sum (fun k _ => Nat.zero_le (f k)) (Finset.mem_univ i)
      rw [hf.1] at this; exact this
    rw [Finset.mem_range]; show f i < j + 1; omega
  · intro r _; rfl
  · intro f _; rfl
  · intro r _; rfl

lemma DD_eq (p : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) :
    dividedDifference p a x = ∑ j ∈ p.support, if a ≤ j then p.coeff j * hh (j - a) x else 0 := by
  unfold dividedDifference
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with h
  · rw [inner_eq a j h]
  · rfl

lemma DD_range (p : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) (N : ℕ) (hN : p.natDegree < N) :
    dividedDifference p a x = ∑ j ∈ Finset.range N, if a ≤ j then p.coeff j * hh (j - a) x else 0 := by
  rw [DD_eq]
  apply Finset.sum_subset
  · intro j hj; rw [Finset.mem_range]; exact lt_of_le_of_lt (le_natDegree_of_mem_supp j hj) hN
  · intro j _ hj
    rw [Polynomial.notMem_support_iff] at hj
    simp [hj]

lemma hh_zero {n : ℕ} (x : Fin n → ℝ) : hh 0 x = 1 := by
  simp [hh]

lemma hh_fin1 (m : ℕ) (x : Fin 1 → ℝ) : hh m x = x 0 ^ m := by
  unfold hh
  have : Finset.piAntidiag (Finset.univ : Finset (Fin 1)) m = {fun _ => m} := by
    ext f
    simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true,
      Finset.mem_singleton, Fin.sum_univ_one]
    constructor
    · intro h; funext i; fin_cases i; exact h
    · intro h; rw [h]
  rw [this, Finset.sum_singleton, Fin.prod_univ_one]

lemma hh_perm (m : ℕ) {n : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : hh m (x ∘ σ) = hh m x := by
  unfold hh
  refine Finset.sum_nbij' (fun f => f ∘ σ.symm) (fun f => f ∘ σ) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_piAntidiag] at hf ⊢
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    rw [← hf.1]; exact Equiv.sum_comp σ.symm f
  · intro f hf
    rw [Finset.mem_piAntidiag] at hf ⊢
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    rw [← hf.1]; exact Equiv.sum_comp σ f
  · intro f _; funext i; simp
  · intro f _; funext i; simp
  · intro f _
    rw [← Equiv.prod_comp σ (fun i => x i ^ (f ∘ σ.symm) i)]
    simp

lemma hh_succ (m : ℕ) {n : ℕ} (x : Fin (n+1) → ℝ) :
    hh (m+1) x = x 0 * hh m x + hh (m+1) (Fin.tail x) := by
  unfold hh
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun f : Fin (n+1) → ℕ => f 0 = 0), add_comm]
  congr 1
  · -- f 0 ≠ 0
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_nbij' (fun g => Fin.cons (g 0 + 1) (Fin.tail g))
      (fun f => Fin.cons (f 0 - 1) (Fin.tail f)) ?_ ?_ ?_ ?_ ?_
    · intro g hg
      rw [Finset.mem_piAntidiag] at hg
      rw [Finset.mem_filter, Finset.mem_piAntidiag]
      refine ⟨⟨?_, fun i _ => Finset.mem_univ i⟩, by simp⟩
      rw [Fin.sum_univ_succ, Fin.cons_zero] at *
      rw [← hg.1]; simp [Fin.tail]; ring
    · intro f hf
      rw [Finset.mem_filter, Finset.mem_piAntidiag] at hf
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      have h1 := hf.1.1
      rw [Fin.sum_univ_succ] at h1 ⊢
      simp only [Fin.cons_zero, Fin.cons_succ]
      simp only [Fin.tail] 
      omega
    · intro g _; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]
    · intro f hf
      rw [Finset.mem_filter] at hf
      ext i; refine Fin.cases ?_ (fun j => ?_) i
      · simp; omega
      · simp [Fin.tail]
    · intro g _
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp [Fin.tail, pow_succ]; ring
  · -- f 0 = 0
    symm
    refine Finset.sum_nbij' (fun g => Fin.cons 0 g) (fun f => Fin.tail f) ?_ ?_ ?_ ?_ ?_
    · intro g hg
      rw [Finset.mem_piAntidiag] at hg
      rw [Finset.mem_filter, Finset.mem_piAntidiag]
      refine ⟨⟨?_, fun i _ => Finset.mem_univ i⟩, by simp⟩
      rw [Fin.sum_univ_succ]; simpa using hg.1
    · intro f hf
      rw [Finset.mem_filter, Finset.mem_piAntidiag] at hf
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      have h1 := hf.1.1
      rw [Fin.sum_univ_succ, hf.2, zero_add] at h1
      exact h1
    · intro g _; rfl
    · intro f hf
      rw [Finset.mem_filter] at hf
      ext i; refine Fin.cases ?_ (fun j => ?_) i
      · simp [hf.2]
      · simp [Fin.tail]
    · intro g _
      rw [Fin.prod_univ_succ]; simp [Fin.tail]


lemma DD_add (p q : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) :
    dividedDifference (p + q) a x = dividedDifference p a x + dividedDifference q a x := by
  set N := p.natDegree + q.natDegree + 1
  rw [DD_range (p + q) a x N (lt_of_le_of_lt (natDegree_add_le _ _) (by omega)),
    DD_range p a x N (by omega), DD_range q a x N (by omega), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp [coeff_add, add_mul]

lemma DD_smul (c : ℝ) (p : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) :
    dividedDifference (C c * p) a x = c * dividedDifference p a x := by
  set N := p.natDegree + 1
  rw [DD_range (C c * p) a x N (lt_of_le_of_lt (natDegree_C_mul_le _ _) (by omega)),
    DD_range p a x N (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp [coeff_C_mul, mul_assoc]

lemma DD_sub (p q : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) :
    dividedDifference (p - q) a x = dividedDifference p a x - dividedDifference q a x := by
  have h := DD_add (p - q) q a x
  rw [sub_add_cancel] at h; linarith

lemma DD_zero_order (p : Polynomial ℝ) (x : Fin 1 → ℝ) : dividedDifference p 0 x = p.eval (x 0) := by
  rw [DD_range p 0 x (p.natDegree + 1) (by omega), eval_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [hh_fin1]

lemma DD_X_mul (p : Polynomial ℝ) (b : ℕ) (x : Fin (b+2) → ℝ) :
    dividedDifference (X * p) (b+1) x =
      x 0 * dividedDifference p (b+1) x + dividedDifference p b (Fin.tail x) := by
  set N := p.natDegree + 1
  rw [DD_range (X * p) (b+1) x (N+1) (lt_of_le_of_lt (natDegree_mul_le) (by
      simp only [natDegree_X]; omega)),
    DD_range p (b+1) x N (by omega), DD_range p b (Fin.tail x) N (by omega),
    Finset.sum_range_succ', Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [Nat.le_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, add_zero, coeff_X_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hbj : b + 1 ≤ j
  · rw [if_pos (show b + 1 ≤ j + 1 by omega), if_pos hbj, if_pos (show b ≤ j by omega)]
    rw [show j + 1 - (b + 1) = (j - (b+1)) + 1 by omega, hh_succ,
      show j - (b+1) + 1 = j - b by omega]
    ring
  · by_cases hb : b = j
    · subst hb
      rw [if_pos (show b + 1 ≤ b + 1 by omega), if_neg hbj, if_pos le_rfl]
      simp [hh_zero]
    · rw [if_neg (show ¬ (b + 1 ≤ j + 1) by omega), if_neg hbj, if_neg (show ¬ (b ≤ j) by omega)]; ring

lemma DD_low (p : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) (h : p.natDegree < a) :
    dividedDifference p a x = 0 := by
  rw [DD_range p a x a h]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  simp at hj; rw [if_neg (by omega)]



/-- powers of the linear matrix polynomial `Y + t E` -/
def Pk {d : ℕ} (Y E : Mat d) (k : ℕ) : Polynomial (Mat d) := (C Y + X * C E) ^ k

lemma Pk_coeff_succ {d : ℕ} (Y E : Mat d) (k j : ℕ) :
    (Pk Y E (k+1)).coeff (j+1) = Y * (Pk Y E k).coeff (j+1) + E * (Pk Y E k).coeff j := by
  unfold Pk
  rw [pow_succ', add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_X_mul, coeff_C_mul]

lemma Pk_coeff_succ_zero {d : ℕ} (Y E : Mat d) (k : ℕ) :
    (Pk Y E (k+1)).coeff 0 = Y * (Pk Y E k).coeff 0 := by
  unfold Pk
  rw [pow_succ', add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_X_mul_zero, add_zero]

lemma Pk_zero {d : ℕ} (Y E : Mat d) (j : ℕ) : (Pk Y E 0).coeff j = if j = 0 then 1 else 0 := by
  unfold Pk; rw [pow_zero, coeff_one]

/-- path sums in an eigenbasis -/
def Path {d : ℕ} (j : ℕ) (lam : Fin d → ℝ) (E' : Mat d) (f : (Fin (j+1) → ℝ) → ℝ) : Mat d :=
  fun a b => ∑ c : Fin (j+1) → Fin d, (if c 0 = a ∧ c (Fin.last j) = b then (1:ℂ) else 0) *
    ((f (fun i => lam (c i)) : ℝ) : ℂ) * ∏ l : Fin j, E' (c l.castSucc) (c l.succ)

lemma Path_add {d j : ℕ} (lam : Fin d → ℝ) (E' : Mat d) (f g : (Fin (j+1) → ℝ) → ℝ) :
    Path j lam E' (fun x => f x + g x) = Path j lam E' f + Path j lam E' g := by
  ext a b; simp only [Path, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_); push_cast; ring

lemma Path_smul {d j : ℕ} (lam : Fin d → ℝ) (E' : Mat d) (r : ℝ) (f : (Fin (j+1) → ℝ) → ℝ) :
    Path j lam E' (fun x => r * f x) = (r : ℂ) • Path j lam E' f := by
  ext a b; simp only [Path, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_); push_cast; ring

lemma Path_congr {d j : ℕ} (lam : Fin d → ℝ) (E' : Mat d) (I : Set ℝ) (hlam : ∀ a, lam a ∈ I)
    (f g : (Fin (j+1) → ℝ) → ℝ) (hfg : ∀ x, (∀ i, x i ∈ I) → f x = g x) :
    Path j lam E' f = Path j lam E' g := by
  ext a b; simp only [Path]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [hfg _ (fun i => hlam _)]

lemma Path_zero {d : ℕ} (lam : Fin d → ℝ) (E' : Mat d) (f : (Fin 1 → ℝ) → ℝ) :
    Path 0 lam E' f = Matrix.diagonal (fun a => ((f (fun _ => lam a) : ℝ) : ℂ)) := by
  ext a b
  simp only [Path, Matrix.diagonal_apply, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rw [← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp]
  have h0 : ∀ c : Fin d, ((Equiv.funUnique (Fin 1) (Fin d)).symm c) 0 = c := fun c => rfl
  have hl : (Fin.last 0 : Fin 1) = 0 := rfl
  simp only [hl, h0]
  by_cases hab : a = b
  · subst hab
    rw [Finset.sum_eq_single a (fun c _ hc => by rw [if_neg (fun h => hc h.1)]; simp) (by simp)]
    simp only [and_self, if_true, one_mul]
    congr 2
  · rw [if_neg hab]
    exact Finset.sum_eq_zero (fun c _ => by rw [if_neg (fun h => hab (h.1.symm.trans h.2))]; simp)


lemma sum_cons' {ι : Type*} [Fintype ι] {n : ℕ} (f : (Fin (n+1) → ι) → ℂ) :
    ∑ x, f x = ∑ x0 : ι, ∑ x' : Fin n → ι, f (Fin.cons x0 x') := by
  rw [← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma Path_mul_x0 {d j : ℕ} (lam : Fin d → ℝ) (E' : Mat d) (f : (Fin (j+1) → ℝ) → ℝ) :
    Path j lam E' (fun x => x 0 * f x) = Matrix.diagonal (fun a => ((lam a : ℝ) : ℂ)) * Path j lam E' f := by
  ext a b
  simp only [Path, Matrix.diagonal_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases h : c 0 = a ∧ c (Fin.last j) = b
  · rw [if_pos h, ← h.1]; push_cast; ring
  · rw [if_neg h]; ring

lemma Path_tail {d j : ℕ} (lam : Fin d → ℝ) (E' : Mat d) (g : (Fin (j+1) → ℝ) → ℝ) :
    Path (j+1) lam E' (fun x => g (Fin.tail x)) = E' * Path j lam E' g := by
  ext a b
  set F := ∑ c' : Fin (j+1) → Fin d, E' a (c' 0) * ((if c' (Fin.last j) = b then (1:ℂ) else 0) *
      ((g (fun i => lam (c' i)) : ℝ) : ℂ) * ∏ l : Fin j, E' (c' l.castSucc) (c' l.succ)) with hF
  have hL : Path (j+1) lam E' (fun x => g (Fin.tail x)) a b = F := by
    simp only [Path]
    rw [sum_cons' (ι := Fin d) (n := j+1)]
    rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl (fun c' _ => ?_)
      have hlast : (Fin.last (j+1) : Fin (j+2)) = (Fin.last j).succ := rfl
      simp only [Fin.cons_zero, hlast, Fin.cons_succ, true_and, Fin.prod_univ_succ, Fin.castSucc_zero,
        Fin.succ_zero_eq_one]
      have h1 : (Fin.cons a c' : Fin (j+2) → Fin d) 1 = c' 0 := rfl
      have h2 : ∀ l : Fin j, (Fin.cons a c' : Fin (j+2) → Fin d) l.succ.castSucc = c' l.castSucc := by
        intro l; rw [← Fin.succ_castSucc, Fin.cons_succ]
      have h3 : ∀ l : Fin j, (Fin.cons a c' : Fin (j+2) → Fin d) l.succ.succ = c' l.succ := by
        intro l; rw [Fin.cons_succ]
      simp only [h1, h2, h3]
      have ht : Fin.tail (fun i => lam ((Fin.cons a c' : Fin (j+2) → Fin d) i)) = fun i => lam (c' i) := by
        funext i; simp [Fin.tail]
      rw [ht]; ring
    · intro x0 _ hx0
      refine Finset.sum_eq_zero (fun c' _ => ?_)
      simp only [Fin.cons_zero]
      rw [if_neg (fun h => hx0 h.1)]; ring
    · simp
  have hR : (E' * Path j lam E' g) a b = F := by
    simp only [Path, Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c' _ => ?_)
    rw [Finset.sum_eq_single (c' 0)]
    · simp only [true_and]
    · intro x _ hx; rw [if_neg (fun h => hx h.1.symm)]; ring
    · simp
  rw [hL, hR]


lemma coeff_path {d : ℕ} {Y : Mat d} (hY : Y.IsHermitian) (E : Mat d) : ∀ (k j : ℕ),
    star (hY.eigenvectorUnitary : Mat d) * (Pk Y E k).coeff j * (hY.eigenvectorUnitary : Mat d) =
      Path j hY.eigenvalues (star (hY.eigenvectorUnitary : Mat d) * E * (hY.eigenvectorUnitary : Mat d))
        (dividedDifference (X ^ k) j) := by
  set U := (hY.eigenvectorUnitary : Mat d) with hUdef
  set D := Matrix.diagonal (fun a => ((hY.eigenvalues a : ℝ) : ℂ)) with hD
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  have hspec : Y = U * D * star U := by
    have := hY.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    rw [this]; rfl
  have hYM : ∀ M : Mat d, star U * (Y * M) * U = D * (star U * M * U) := by
    intro M
    rw [hspec]
    calc star U * (U * D * star U * M) * U = (star U * U) * D * (star U * M * U) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, Matrix.one_mul]
  have hEM : ∀ M : Mat d, star U * (E * M) * U = (star U * E * U) * (star U * M * U) := by
    intro M
    calc star U * (E * M) * U = star U * E * (U * star U) * M * U := by
          rw [hUU', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  intro k
  induction k with
  | zero =>
    intro j
    rw [Pk_zero]
    cases j with
    | zero =>
      rw [if_pos rfl, Matrix.mul_one, hUU, Path_zero]
      ext a b
      simp [DD_zero_order, Matrix.diagonal_apply, Matrix.one_apply]
    | succ j =>
      rw [if_neg (by omega), Matrix.mul_zero, Matrix.zero_mul]
      have : (dividedDifference (X ^ 0 : Polynomial ℝ) (j+1)) = fun _ => 0 := by
        funext x; exact DD_low _ _ _ (by simp)
      rw [this]
      ext a b; simp [Path]
  | succ k ih =>
    intro j
    cases j with
    | zero =>
      rw [Pk_coeff_succ_zero, hYM, ih 0, Path_zero, Path_zero]
      ext a b
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, hD, mul_ite, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, DD_zero_order]
      split_ifs with hab
      · subst hab; simp [pow_succ']
      · simp
    | succ j =>
      rw [Pk_coeff_succ, Matrix.mul_add, Matrix.add_mul, hYM, hEM, ih (j+1), ih j]
      rw [← Path_mul_x0, ← Path_tail, ← Path_add]
      congr 1
      funext x
      rw [pow_succ', DD_X_mul]

lemma path_prod {ι : Type*} [Fintype ι] [DecidableEq ι] : ∀ (k : ℕ) (B : Fin k → Matrix ι ι ℂ) (a b : ι),
    (List.ofFn B).prod a b = ∑ u : Fin (k+1) → ι,
      (if u 0 = a ∧ u (Fin.last k) = b then (1:ℂ) else 0) * ∏ i : Fin k, B i (u i.castSucc) (u i.succ)
  | 0, B, a, b => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    have h0 : ∀ c : ι, ((Equiv.funUnique (Fin 1) ι).symm c) 0 = c := fun c => rfl
    have hl : (Fin.last 0 : Fin 1) = 0 := rfl
    simp only [hl, h0]
    rw [Matrix.one_apply]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg h]; symm
      exact Finset.sum_eq_zero (fun c _ => if_neg (fun hc => h (hc.1.symm.trans hc.2)))
  | k+1, B, a, b => by
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp_rw [path_prod k]
    rw [← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.prod_univ_succ, Fin.castSucc_zero,
      Fin.succ_zero_eq_one, Fin.cons_one, Fin.castSucc_succ, Fin.cons_succ, ← Fin.succ_last]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_eq_single (u 0)]
      · by_cases hb : u (Fin.last k) = b <;> simp [hb]
      · intro c _ hc; simp [Ne.symm hc]
      · simp
    · intro c _ hc; refine Finset.sum_eq_zero (fun u _ => ?_); simp [hc]
    · simp


lemma Path_sum {d j : ℕ} {L : ℕ} (lam : Fin d → ℝ) (E' : Mat d) (f : Fin L → (Fin (j+1) → ℝ) → ℝ) :
    Path j lam E' (fun x => ∑ α, f α x) = ∑ α, Path j lam E' (f α) := by
  ext a b; simp only [Path, Matrix.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  push_cast; rw [Finset.mul_sum, Finset.sum_mul]

lemma Path_prod {d j : ℕ} (lam : Fin d → ℝ) (E' : Mat d) (g : Fin (j+1) → ℝ → ℝ) :
    Path j lam E' (fun x => ∏ i, g i (x i)) =
      (List.ofFn (fun l : Fin j => Matrix.diagonal (fun a => ((g l.castSucc (lam a) : ℝ) : ℂ)) * E')).prod *
        Matrix.diagonal (fun a => ((g (Fin.last j) (lam a) : ℝ) : ℂ)) := by
  ext a b
  rw [Matrix.mul_diagonal, path_prod]
  simp only [Path, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [Matrix.diagonal_mul]
  by_cases h : c 0 = a ∧ c (Fin.last j) = b
  · rw [if_pos h, ← h.2]
    push_cast
    rw [Fin.prod_univ_castSucc (fun i => ((g i (lam (c i)) : ℝ) : ℂ))]
    rw [Finset.prod_mul_distrib]
    ring
  · rw [if_neg h]; ring


lemma conj_prod {d : ℕ} (U : Mat d) (hUU : star U * U = 1) (E : Mat d) : ∀ (j : ℕ) (D : Fin (j+1) → Mat d),
    U * ((List.ofFn (fun l : Fin j => D l.castSucc * (star U * E * U))).prod * D (Fin.last j)) * star U =
      (List.ofFn (fun l : Fin j => (U * D l.castSucc * star U) * E)).prod * (U * D (Fin.last j) * star U)
  | 0, D => by simp
  | j+1, D => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have ih := conj_prod U hUU E j (fun i => D i.succ)
    simp only [Fin.succ_castSucc] at ih ⊢
    have hl : (Fin.last (j+1) : Fin (j+2)) = (Fin.last j).succ := rfl
    rw [hl]
    calc U * (D (Fin.castSucc 0) * (star U * E * U) *
          (List.ofFn fun l : Fin j => D l.succ.castSucc * (star U * E * U)).prod * D (Fin.last j).succ) * star U
        = (U * D (Fin.castSucc 0) * star U) * E * (U * ((List.ofFn fun l : Fin j => D l.succ.castSucc * (star U * E * U)).prod *
            D (Fin.last j).succ) * star U) := by
          simp only [Matrix.mul_assoc]
          try rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
      _ = _ := by
          rw [ih]
          simp only [Matrix.mul_assoc]


lemma exprPow_var {d : ℕ} : ∀ k : ℕ, exprPow (exprVar d true) k = [⟨List.replicate k ((1 : Mat d), true), 1⟩]
  | 0 => rfl
  | k+1 => by
    rw [exprPow, exprPow_var k]
    simp [exprMul, exprVar, wordMul, List.replicate_succ']

lemma univariate_words {d : ℕ} (K : ℕ) :
    (univariate d K).words = (q K).support.toList.map (fun k =>
      (⟨List.replicate k ((1 : Mat d), true), (((q K).coeff k : ℝ) : ℂ) • 1⟩ : Word d)) := by
  simp only [univariate, traceExpr, exprPoly, exprPow_var, exprScale]
  induction (q K).support.toList with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.map_cons, List.map_nil, List.singleton_append] at ih ⊢; rw [ih]

lemma wordLine_rep {d : ℕ} (k : ℕ) (c : ℂ) (X Y E₀ E₁ : Mat d) :
    wordLine (⟨List.replicate k ((1 : Mat d), true), c • 1⟩ : Word d) X Y E₀ E₁ =
      Pk Y E₁ k * C (c • 1) := by
  unfold wordLine Pk
  simp [List.map_replicate, List.prod_replicate]

lemma taylor_univariate {d : ℕ} (K : ℕ) (X Y E₀ E₁ : Mat d) (j : ℕ) (hj : 1 ≤ j) :
    OptimalTraceDistance.Estimation.taylor (univariate d K) X Y j E₀ E₁ =
      (∑ k ∈ (q K).support, ((((q K).coeff k : ℝ) : ℂ)) • (Pk Y E₁ k).coeff j).trace := by
  unfold OptimalTraceDistance.Estimation.taylor
  rw [if_neg (by omega)]
  simp only [univariate_words, List.map_map, Function.comp_def, wordLine_rep, coeff_mul_C]
  have : (univariate d K).constant = 0 := rfl
  rw [zero_add, Matrix.trace_sum]
  rw [Finset.sum_map_toList]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]


section cfcsec
variable {d : ℕ}
lemma quad_conj (U : Mat d) (B : Mat d) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((U * B * star U) *ᵥ x) = star (star U *ᵥ x) ⬝ᵥ (B *ᵥ (star U *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  simp [Matrix.star_eq_conjTranspose]

lemma quad_diag (w : Fin d → ℂ) (y : Fin d → ℂ) :
    star y ⬝ᵥ (diagonal w *ᵥ y) = ∑ i, w i * (star (y i) * y i) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => by ring)

lemma quad_cfc {A : Mat d} (hA : A.IsHermitian) (f : ℝ → ℝ) (x : Fin d → ℂ) :
    star x ⬝ᵥ (cfc f A *ᵥ x) =
      ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) *
        (star ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i) *
          ((star (hA.eigenvectorUnitary : Mat d) *ᵥ x) i)) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, quad_conj, quad_diag]
  rfl

lemma unitary_norm (U : Mat d) (hU : U ∈ unitary (Mat d)) (x : Fin d → ℂ) :
    star (star U *ᵥ x) ⬝ᵥ (star U *ᵥ x) = star x ⬝ᵥ x := by
  have := quad_conj U 1 x
  rw [mul_one, Unitary.mul_star_self_of_mem hU, one_mulVec, one_mulVec] at this
  exact this.symm

lemma sum_normsq (y : Fin d → ℂ) : star y ⬝ᵥ y = ∑ i, ((‖y i‖^2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]
  show y i * (starRingEnd ℂ) (y i) = _
  rw [Complex.mul_conj', Complex.ofReal_pow]


lemma inner_eq' (A : Mat d) (x : EuclideanSpace ℂ (Fin d)) :
    RCLike.re (inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) A x) x) =
      (star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  simp only [dotProduct, Pi.star_apply, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma normsq_eq (x : EuclideanSpace ℂ (Fin d)) :
    ‖x‖^2 = (star (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

lemma opNorm_le_of_quad {A : Mat d} (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Fin d → ℂ, |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ c * (star x ⬝ᵥ x).re) :
    opNorm A ≤ c := by
  unfold opNorm
  have hT : (Matrix.toEuclideanCLM (𝕜 := ℂ) A : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] _).IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hT]
  refine ciSup_le (fun x => ?_)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf]
  rw [inner_eq', normsq_eq]
  rcases eq_or_lt_of_le (sq_nonneg ‖x‖) with h0 | hpos
  · rw [normsq_eq] at h0; rw [← h0]; simp [hc]
  · rw [normsq_eq] at hpos
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact h _


section spec
variable {A : Mat d} (hA : A.IsHermitian)
include hA

lemma U_mem : (hA.eigenvectorUnitary : Mat d) ∈ unitary (Mat d) := (hA.eigenvectorUnitary).2

lemma cfc_explicit (f : ℝ → ℝ) : cfc f A =
    (hA.eigenvectorUnitary : Mat d) * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Mat d) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl

lemma cfc_herm (f : ℝ → ℝ) : (cfc f A).IsHermitian := by
  rw [cfc_explicit hA]
  exact isHermitian_mul_mul_conjTranspose _
    (isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp [Complex.conj_ofReal]))

end spec

lemma opNorm_cfc_le {Y : Mat d} (hY : Y.IsHermitian) (g : ℝ → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hb : ∀ a, |g (hY.eigenvalues a)| ≤ B) : opNorm (cfc g Y) ≤ B := by
  refine opNorm_le_of_quad (cfc_herm hY g) hB0 (fun x => ?_)
  rw [quad_cfc hY g x]
  set y := star (hY.eigenvectorUnitary : Mat d) *ᵥ x
  have hyy : (star x ⬝ᵥ x) = star y ⬝ᵥ y := (unitary_norm _ (U_mem hY) x).symm
  rw [hyy, sum_normsq y]
  simp only [Complex.re_sum, Complex.ofReal_re]
  have h1 : ∀ i, (((g (hY.eigenvalues i) : ℝ) : ℂ) * (star (y i) * y i)).re = g (hY.eigenvalues i) * ‖y i‖^2 := by
    intro i
    have : star (y i) * y i = ((‖y i‖^2 : ℝ) : ℂ) := by
      rw [mul_comm]; show y i * (starRingEnd ℂ) (y i) = _
      rw [Complex.mul_conj', Complex.ofReal_pow]
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [h1]
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖y i‖)]
  exact mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _)

end cfcsec


lemma opNorm_nonneg' {d : ℕ} (A : Mat d) : 0 ≤ opNorm A := norm_nonneg _

lemma Path_finsum {d j : ℕ} {S : Type*} (s : Finset S) (lam : Fin d → ℝ) (E' : Mat d)
    (f : S → (Fin (j+1) → ℝ) → ℝ) :
    Path j lam E' (fun x => ∑ k ∈ s, f k x) = ∑ k ∈ s, Path j lam E' (f k) := by
  ext a b; simp only [Path, Matrix.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  push_cast; rw [Finset.mul_sum, Finset.sum_mul]

lemma DD_monomial_sum (p : Polynomial ℝ) (j : ℕ) (x : Fin (j+1) → ℝ) :
    dividedDifference p j x = ∑ k ∈ p.support, p.coeff k * dividedDifference (X ^ k) j x := by
  rw [DD_eq]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [DD_range (X ^ k) j x (k+1) (by simp)]
  rw [Finset.sum_eq_single k]
  · simp [Polynomial.coeff_X_pow_self]
  · intro b _ hb; simp [Polynomial.coeff_X_pow, hb]
  · simp

lemma trace_conj {d : ℕ} (U M : Mat d) (hUU : U * star U = 1) : M.trace = (star U * M * U).trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]

lemma sum_coeff_path {d : ℕ} {Y : Mat d} (hY : Y.IsHermitian) (p : Polynomial ℝ) (E : Mat d) (j : ℕ) :
    star (hY.eigenvectorUnitary : Mat d) * (∑ k ∈ p.support, ((p.coeff k : ℝ) : ℂ) • (Pk Y E k).coeff j) *
      (hY.eigenvectorUnitary : Mat d) =
    Path j hY.eigenvalues (star (hY.eigenvectorUnitary : Mat d) * E * (hY.eigenvectorUnitary : Mat d))
      (dividedDifference p j) := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, coeff_path hY E]
  have : dividedDifference p j = fun x => ∑ k ∈ p.support, p.coeff k * dividedDifference (X ^ k) j x := by
    funext x; exact DD_monomial_sum p j x
  rw [this, Path_finsum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Path_smul]

theorem uni_rep {d K j : ℕ} (hj : 1 ≤ j) {Y : Mat d} (hY : Y.IsHermitian) {I : Set ℝ}
    (hspec : ∀ a, hY.eigenvalues a ∈ I) {M : ℝ}
    (hsep : HasSeparatedBound j I (dividedDifference (q K) j) M) (X : Mat d) :
    HasOrderedBound j (OptimalTraceDistance.Estimation.taylor (univariate d K) X Y j) M := by
  obtain ⟨L, c, g, B, hB, hid, hbd⟩ := hsep
  set U := (hY.eigenvectorUnitary : Mat d) with hU
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  refine ⟨L, fun α => ((c α : ℝ) : ℂ), fun α i => cfc (g α i) Y, fun _ _ => true, ?_, ?_⟩
  · intro E₀ E₁
    rw [taylor_univariate _ _ _ _ _ _ hj, trace_conj U _ hUU', sum_coeff_path hY (q K) E₁ j]
    rw [Path_congr _ _ I hspec _ (fun x => ∑ α, c α * ∏ i, g α i (x i)) hid]
    rw [Path_sum]
    simp only [Path_smul, Path_prod, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    congr 1
    rw [trace_conj (star U) _ (by rw [star_star]; exact hUU), star_star]
    rw [conj_prod U hUU E₁ j (fun i => Matrix.diagonal (fun a => ((g α i (hY.eigenvalues a) : ℝ) : ℂ)))]
    simp only [if_true, cfc_explicit hY]
    rfl
  · refine le_trans (Finset.sum_le_sum (fun α _ => ?_)) hbd
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine Finset.prod_le_prod (fun i _ => opNorm_nonneg' _) (fun i _ => ?_)
    exact opNorm_cfc_le hY _ (hB α i).1 (fun a => (hB α i).2 _ (hspec a))

lemma card_tuples (a m k : ℕ) (hmk : m ≤ k) :
    ((Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (k+1))).filter
      (fun r => (∑ i, r i (Finset.mem_univ i)) = m)).card = (a + m).choose m := by
  have h1 : ((Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (k+1))).filter
      (fun r => (∑ i, r i (Finset.mem_univ i)) = m)).card =
      (Finset.piAntidiag (Finset.univ : Finset (Fin (a+1))) m).card := by
    refine Finset.card_nbij' (fun r i => r i (Finset.mem_univ i)) (fun f i _ => f i) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Finset.mem_coe, Finset.mem_filter] at hr
      rw [Finset.mem_coe, Finset.mem_piAntidiag]
      exact ⟨hr.2, fun i _ => Finset.mem_univ i⟩
    · intro f hf
      rw [Finset.mem_coe, Finset.mem_piAntidiag] at hf
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_pi]
      refine ⟨fun i _ => ?_, hf.1⟩
      have h3 : f i ≤ m := calc f i ≤ Finset.univ.sum f :=
            Finset.single_le_sum (f := f) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = m := hf.1
      rw [Finset.mem_range]; show f i < k + 1; omega
    · intro r _; rfl
    · intro f _; rfl
  rw [h1, ← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ, Finset.card_univ,
    Sym.card_sym_fin_eq_multichoose, Nat.multichoose_eq]
  congr 1; omega

lemma dd_repeated (p : Polynomial ℝ) (a : ℕ) (x : ℝ) :
    (a.factorial : ℝ) * dividedDifference p a (fun _ => x) = (derivative^[a] p).eval x := by
  conv_rhs => rw [p.as_sum_support_C_mul_X_pow]
  rw [Polynomial.iterate_derivative_sum, Polynomial.eval_finsetSum, dividedDifference,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_smul,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_smul, Polynomial.eval_pow,
    Polynomial.eval_X, smul_eq_mul]
  split_ifs with hk
  · have hprod : ∀ r ∈ (Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (k+1))).filter
        (fun r => (∑ i, r i (Finset.mem_univ i)) = k - a),
        ∏ i, x ^ (r i (Finset.mem_univ i)) = x ^ (k - a) := by
      intro r hr
      rw [Finset.prod_pow_eq_pow_sum, (Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl hprod, Finset.sum_const, card_tuples a (k - a) k (by omega), nsmul_eq_mul,
      show a + (k - a) = k by omega, Nat.choose_symm hk, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]; simp



lemma trace_Path1 {d : ℕ} (lam : Fin d → ℝ) (E' : Mat d) (f : (Fin 2 → ℝ) → ℝ) :
    (Path 1 lam E' f).trace = ∑ a, ((f (fun _ => lam a) : ℝ) : ℂ) * E' a a := by
  simp only [Matrix.trace, Matrix.diag, Path]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single (fun _ => a)]
  · simp only [and_self, if_true, one_mul, Fin.prod_univ_one]
  · intro c _ hc
    rw [if_neg]; · ring
    rintro ⟨h0, h1⟩
    apply hc; funext i
    fin_cases i
    · exact h0
    · exact h1
  · simp

lemma opNorm_one_le' {d : ℕ} : opNorm (1 : Mat d) ≤ 1 := by
  unfold opNorm; rw [map_one]; exact ContinuousLinearMap.norm_id_le

theorem uni_rep1 {d K : ℕ} {Y : Mat d} (hY : Y.IsHermitian) (X : Mat d) {B : ℝ} (hB0 : 0 ≤ B)
    (hb : ∀ a, |(q K).derivative.eval (hY.eigenvalues a)| ≤ B) :
    HasOrderedBound 1 (OptimalTraceDistance.Estimation.taylor (univariate d K) X Y 1) B := by
  set U := (hY.eigenvectorUnitary : Mat d) with hU
  have hUU' : U * star U = 1 := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  set Aq := cfc (fun x => (q K).derivative.eval x) Y
  refine ⟨1, fun _ => 1, fun _ i => if i = 0 then Aq else 1, fun _ _ => true, ?_, ?_⟩
  · intro E₀ E₁
    rw [taylor_univariate _ _ _ _ _ _ le_rfl, trace_conj U _ hUU', sum_coeff_path hY (q K) E₁ 1, trace_Path1]
    simp only [Fin.sum_univ_one, one_mul, if_true, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
      List.prod_nil, Matrix.mul_one]
    have hl : (Fin.last 1 : Fin 2) ≠ 0 := by decide
    rw [if_neg hl, Matrix.mul_one]
    have h0 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := rfl
    rw [if_pos h0, trace_conj U _ hUU']
    rw [show Aq = U * Matrix.diagonal (fun a => (((q K).derivative.eval (hY.eigenvalues a) : ℝ) : ℂ)) * star U
      from cfc_explicit hY _]
    have : star U * (U * Matrix.diagonal (fun a => (((q K).derivative.eval (hY.eigenvalues a) : ℝ) : ℂ)) * star U * E₁) * U
        = Matrix.diagonal (fun a => (((q K).derivative.eval (hY.eigenvalues a) : ℝ) : ℂ)) * (star U * E₁ * U) := by
      have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
      calc star U * (U * Matrix.diagonal _ * star U * E₁) * U
          = (star U * U) * Matrix.diagonal (fun a => (((q K).derivative.eval (hY.eigenvalues a) : ℝ) : ℂ)) *
            (star U * E₁ * U) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hUU, Matrix.one_mul]
    rw [this]
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 2
    have := dd_repeated (q K) 1 (hY.eigenvalues a)
    simp only [Nat.factorial_one, Nat.cast_one, one_mul, Function.iterate_one] at this
    exact this
  · simp only [Finset.univ_unique, Finset.sum_singleton, norm_one, one_mul]
    rw [Fin.prod_univ_two]
    have hl : (1 : Fin 2) ≠ 0 := by decide
    rw [if_pos rfl, if_neg hl]
    have h1 := opNorm_cfc_le hY (fun x => (q K).derivative.eval x) hB0 hb
    calc opNorm Aq * opNorm (1 : Mat d) ≤ B * 1 :=
          mul_le_mul h1 opNorm_one_le' (opNorm_nonneg' _) hB0
      _ = B := mul_one B

lemma sep_mono {a : ℕ} {I : Set ℝ} {f : (Fin (a+1) → ℝ) → ℝ} {M M' : ℝ}
    (h : HasSeparatedBound a I f M) (hM : M ≤ M') : HasSeparatedBound a I f M' := by
  obtain ⟨L, c, g, B, hB, hrep, hs⟩ := h
  exact ⟨L, c, g, B, hB, hrep, hs.trans hM⟩

lemma sep_congr {a : ℕ} {I : Set ℝ} {f f' : (Fin (a+1) → ℝ) → ℝ} {M : ℝ}
    (h : HasSeparatedBound a I f M) (he : ∀ x, (∀ i, x i ∈ I) → f' x = f x) :
    HasSeparatedBound a I f' M := by
  obtain ⟨L, c, g, B, hB, hrep, hs⟩ := h
  exact ⟨L, c, g, B, hB, fun x hx => (he x hx).trans (hrep x hx), hs⟩

lemma sep_zero (a : ℕ) (I : Set ℝ) : HasSeparatedBound a I (fun _ => 0) 0 :=
  ⟨0, Fin.elim0, fun α => Fin.elim0 α, fun α => Fin.elim0 α, fun α => Fin.elim0 α,
    fun x _ => by simp, by simp⟩

lemma sep_add {a : ℕ} {I : Set ℝ} {f₁ f₂ : (Fin (a+1) → ℝ) → ℝ} {M₁ M₂ : ℝ}
    (h₁ : HasSeparatedBound a I f₁ M₁) (h₂ : HasSeparatedBound a I f₂ M₂) :
    HasSeparatedBound a I (fun x => f₁ x + f₂ x) (M₁ + M₂) := by
  obtain ⟨L₁, c₁, g₁, B₁, hB₁, hr₁, hs₁⟩ := h₁
  obtain ⟨L₂, c₂, g₂, B₂, hB₂, hr₂, hs₂⟩ := h₂
  refine ⟨L₁ + L₂, Fin.append c₁ c₂, Fin.append g₁ g₂, Fin.append B₁ B₂, ?_, ?_, ?_⟩
  · intro α i
    refine Fin.addCases (fun α => ?_) (fun α => ?_) α
    · simp only [Fin.append_left]; exact hB₁ α i
    · simp only [Fin.append_right]; exact hB₂ α i
  · intro x hx
    beta_reduce
    rw [Fin.sum_univ_add, hr₁ x hx, hr₂ x hx]
    simp [Fin.append_left, Fin.append_right]
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    linarith

lemma sep_smul {a : ℕ} {I : Set ℝ} {f : (Fin (a+1) → ℝ) → ℝ} {M : ℝ} (r : ℝ)
    (h : HasSeparatedBound a I f M) : HasSeparatedBound a I (fun x => r * f x) (|r| * M) := by
  obtain ⟨L, c, g, B, hB, hrep, hs⟩ := h
  refine ⟨L, fun α => r * c α, g, B, hB, fun x hx => ?_, ?_⟩
  · beta_reduce; rw [hrep x hx, Finset.mul_sum]; simp only [mul_assoc]
  · simp only [abs_mul, mul_assoc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hs (abs_nonneg r)

lemma sep_sum {a : ℕ} {I : Set ℝ} (n : ℕ) {f : ℕ → (Fin (a+1) → ℝ) → ℝ} {M : ℕ → ℝ}
    (h : ∀ m < n, HasSeparatedBound a I (f m) (M m)) :
    HasSeparatedBound a I (fun x => ∑ m ∈ Finset.range n, f m x) (∑ m ∈ Finset.range n, M m) := by
  induction n with
  | zero => simpa using sep_zero a I
  | succ n ih =>
    have := sep_add (ih (fun m hm => h m (by omega))) (h n (by omega))
    simpa [Finset.sum_range_succ] using this


/-- Chebyshev antiderivative pieces -/
def Qc (l : ℕ) : Polynomial ℝ :=
  if l = 0 then 0 else if l = 1 then C (1/4) * Chebyshev.T ℝ 2 else
    C (1 / (2 * ((l:ℝ) + 1))) * Chebyshev.T ℝ ((l:ℤ) + 1) - C (1 / (2 * ((l:ℝ) - 1))) * Chebyshev.T ℝ ((l:ℤ) - 1)

lemma U_sub_U' (n : ℤ) : Chebyshev.U ℝ (n + 2) - Chebyshev.U ℝ n = 2 * Chebyshev.T ℝ (n + 2) := by
  rw [Chebyshev.T_eq_X_mul_U_sub_U, Chebyshev.U_add_two]; ring

lemma Qc_deriv (l : ℕ) (hl : 1 ≤ l) : derivative (Qc l) = Chebyshev.T ℝ l := by
  unfold Qc
  rw [if_neg (by omega)]
  by_cases h1 : l = 1
  · subst h1
    simp only [if_true, derivative_C_mul]
    rw [show ((2:ℤ) : ℤ) = (2 : ℤ) from rfl]
    have hT2 : Chebyshev.T ℝ (2 : ℕ) = Chebyshev.T ℝ ((2:ℤ)) := rfl
    rw [Chebyshev.T_derivative_eq_U, show ((2:ℤ) - 1) = 1 by norm_num, Chebyshev.U_one]
    simp only [Nat.cast_one, Chebyshev.T_one, Int.cast_ofNat]
    rw [show (2 : Polynomial ℝ) = C 2 from (map_ofNat C 2).symm]
    calc C (1/4 : ℝ) * (C 2 * (C 2 * X)) = C (1/4 * 2 * 2) * X := by simp only [C_mul]; ring
      _ = X := by norm_num
  · rw [if_neg h1]
    rw [derivative_sub, derivative_C_mul, derivative_C_mul, Chebyshev.T_derivative_eq_U,
      Chebyshev.T_derivative_eq_U]
    have hl2 : (2:ℝ) ≤ l := by exact_mod_cast (by omega : 2 ≤ l)
    have e1 : ((l:ℤ) + 1 - 1) = (l:ℤ) := by ring
    have e2 : ((l:ℤ) - 1 - 1) = ((l:ℤ) - 2) := by ring
    rw [e1, e2]
    have hU := U_sub_U' ((l:ℤ) - 2)
    rw [show (l:ℤ) - 2 + 2 = l by ring] at hU
    push_cast
    have hne1 : ((l:ℝ) + 1) ≠ 0 := by positivity
    have hne2 : ((l:ℝ) - 1) ≠ 0 := by linarith
    have hc1 : ((l : Polynomial ℝ) + 1) = C ((l:ℝ) + 1) := by rw [C_add, C_1, C_eq_natCast]
    have hc2 : ((l : Polynomial ℝ) - 1) = C ((l:ℝ) - 1) := by rw [C_sub, C_1, C_eq_natCast]
    rw [hc1, hc2, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul]
    rw [show 1 / (2 * ((l:ℝ) + 1)) * ((l:ℝ) + 1) = 1/2 by field_simp,
      show 1 / (2 * ((l:ℝ) - 1)) * ((l:ℝ) - 1) = 1/2 by field_simp]
    rw [← mul_sub, hU, ← mul_assoc]
    rw [show (C (1/2 : ℝ) : Polynomial ℝ) * 2 = 1 by
      rw [show (2 : Polynomial ℝ) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num, one_mul]


/-- Chebyshev coefficients of `q K'` -/
def cJ (K l : ℕ) : ℝ := if l = 0 then 0 else
  4 * Real.sin (Real.pi * l / 2) / (Real.pi * l) *
    ∫ t in (-Real.pi)..Real.pi, jackson (K / 2 + 1) t * Real.cos (l*t)

def Rq (K : ℕ) : Polynomial ℝ := ∑ l ∈ Finset.range K, C (cJ K l) * Qc l

lemma jD_eq (K : ℕ) : jacksonDerivative K = ∑ l ∈ Finset.range K, C (cJ K l) * Chebyshev.T ℝ l := rfl

lemma Rq_deriv (K : ℕ) : derivative (Rq K) = jacksonDerivative K := by
  rw [Rq, derivative_sum, jD_eq]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [derivative_C_mul]
  by_cases hl : l = 0
  · subst hl; simp [cJ]
  · rw [Qc_deriv l (by omega)]

lemma q_eq_Rq (K : ℕ) : ∃ c : ℝ, q K = Rq K + C c := by
  have h : derivative (q K - Rq K) = 0 := by
    rw [derivative_sub, OTDJackson.q_derivative, Rq_deriv, sub_self]
  rw [Polynomial.derivative_eq_zero] at h
  refine ⟨(q K - Rq K).coeff 0, ?_⟩
  have := Polynomial.eq_C_of_natDegree_eq_zero h
  rw [← this]; ring

lemma DD_const (c : ℝ) (j : ℕ) (hj : 1 ≤ j) (x : Fin (j+1) → ℝ) : dividedDifference (C c) j x = 0 :=
  DD_low _ _ _ (by rw [natDegree_C]; omega)

lemma DD_finsum (s : Finset ℕ) (c : ℕ → ℝ) (P : ℕ → Polynomial ℝ) (j : ℕ) (x : Fin (j+1) → ℝ) :
    dividedDifference (∑ l ∈ s, C (c l) * P l) j x = ∑ l ∈ s, c l * dividedDifference (P l) j x := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (0 : Polynomial ℝ) = C 0 by simp]
    by_cases hj : 1 ≤ j
    · exact DD_const 0 j hj x
    · have : j = 0 := by omega
      subst this; rw [DD_zero_order]; simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DD_add, DD_smul, ih]

lemma DD_q (K j : ℕ) (hj : 1 ≤ j) (x : Fin (j+1) → ℝ) :
    dividedDifference (q K) j x = ∑ l ∈ Finset.range K, cJ K l * dividedDifference (Qc l) j x := by
  obtain ⟨c, hc⟩ := q_eq_Rq K
  rw [hc, DD_add, DD_const c j hj x, add_zero, Rq, DD_finsum]

lemma sepT (j m : ℕ) (hj : 1 ≤ j) :
    HasSeparatedBound j (Set.Icc (-(1/2)) (1/2)) (dividedDifference (Chebyshev.T ℝ m) j)
      ((4 * (m:ℝ))^j / (j.factorial : ℝ)) := by
  by_cases hm : j ≤ m
  · exact (lemma_B_1 m j hj hm).2.1
  · refine sep_mono (sep_congr (sep_zero j _) (fun x _ => ?_)) (by positivity)
    exact DD_low _ _ _ (by rw [Chebyshev.natDegree_T]; simp; omega)

def bQ (j l : ℕ) : ℝ :=
  if l = 0 then 0 else if l = 1 then (1/4) * ((4 * 2)^j / (j.factorial : ℝ)) else
    (1 / (2 * ((l:ℝ) + 1))) * ((4 * ((l:ℝ) + 1))^j / (j.factorial : ℝ)) +
      (1 / (2 * ((l:ℝ) - 1))) * ((4 * ((l:ℝ) - 1))^j / (j.factorial : ℝ))

lemma sepQ (j l : ℕ) (hj : 1 ≤ j) :
    HasSeparatedBound j (Set.Icc (-(1/2)) (1/2)) (dividedDifference (Qc l) j) (bQ j l) := by
  unfold bQ
  by_cases h0 : l = 0
  · subst h0; simp only [if_true, Qc]
    refine sep_congr (sep_zero j _) (fun x _ => ?_)
    rw [show (0 : Polynomial ℝ) = C 0 by simp]; exact DD_const 0 j hj x
  · rw [if_neg h0]
    by_cases h1 : l = 1
    · subst h1
      simp only [if_true, Qc, one_ne_zero, if_false]
      have := sep_smul (1/4) (sepT j 2 hj)
      rw [abs_of_pos (by norm_num)] at this
      refine sep_congr this (fun x _ => ?_)
      rw [DD_smul]; push_cast; rfl
    · rw [if_neg h1]
      have hl2 : (2:ℝ) ≤ l := by exact_mod_cast (by omega : 2 ≤ l)
      have hl1 : (0:ℝ) < (l:ℝ) - 1 := by linarith
      have e3 : ((l - 1 : ℕ) : ℝ) = (l:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hQ : Qc l = C (1 / (2 * ((l:ℝ) + 1))) * Chebyshev.T ℝ (((l+1 : ℕ) : ℤ)) +
          C (-(1 / (2 * ((l:ℝ) - 1)))) * Chebyshev.T ℝ (((l-1 : ℕ) : ℤ)) := by
        simp only [Qc, h0, h1, if_false]
        rw [sub_eq_add_neg, ← neg_mul, ← C_neg]
        have e1 : (((l+1 : ℕ) : ℤ)) = (l:ℤ) + 1 := by push_cast; rfl
        have e2 : (((l-1 : ℕ) : ℤ)) = (l:ℤ) - 1 := by rw [Nat.cast_sub (by omega)]; rfl
        rw [e1, e2]
      have hA := sep_smul (1 / (2 * ((l:ℝ) + 1))) (sepT j (l+1) hj)
      have hB := sep_smul (-(1 / (2 * ((l:ℝ) - 1)))) (sepT j (l-1) hj)
      have hsum := sep_add hA hB
      refine sep_mono (sep_congr hsum (fun x _ => by rw [hQ, DD_add, DD_smul, DD_smul])) (le_of_eq ?_)
      rw [abs_of_pos (by positivity), abs_neg, abs_of_pos (by positivity), e3]
      push_cast; ring


lemma bQ_le (j l : ℕ) (hj : 1 ≤ j) (hl : 1 ≤ l) :
    bQ j l ≤ 4^j * ((l:ℝ) + 1)^(j-1) / (j.factorial : ℝ) := by
  have hf : (0:ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold bQ
  rw [if_neg (by omega)]
  by_cases h1 : l = 1
  · subst h1; rw [if_pos rfl]
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hf]
    simp only [Nat.cast_one]
    rw [show ((1:ℝ)+1) = 2 by norm_num, mul_pow, pow_succ (4:ℝ), pow_succ (2:ℝ)]
    nlinarith [pow_pos (show (0:ℝ) < 4 by norm_num) m, pow_pos (show (0:ℝ) < 2 by norm_num) m,
      mul_pos (pow_pos (show (0:ℝ) < 4 by norm_num) m) (pow_pos (show (0:ℝ) < 2 by norm_num) m)]
  · rw [if_neg h1]
    have hl2 : (2:ℝ) ≤ l := by exact_mod_cast (by omega : 2 ≤ l)
    have hl1 : (0:ℝ) < (l:ℝ) - 1 := by linarith
    have hA : 1 / (2 * ((l:ℝ) + 1)) * ((4 * ((l:ℝ) + 1))^(m+1) / (((m+1).factorial : ℕ) : ℝ)) =
        4^(m+1) * ((l:ℝ)+1)^m / (2 * (((m+1).factorial : ℕ) : ℝ)) := by
      field_simp; rw [mul_pow, pow_succ ((l:ℝ)+1)]; ring
    have hB : 1 / (2 * ((l:ℝ) - 1)) * ((4 * ((l:ℝ) - 1))^(m+1) / (((m+1).factorial : ℕ) : ℝ)) =
        4^(m+1) * ((l:ℝ)-1)^m / (2 * (((m+1).factorial : ℕ) : ℝ)) := by
      field_simp; rw [mul_pow, pow_succ ((l:ℝ)-1)]; ring
    rw [hA, hB]
    have hmono : ((l:ℝ) - 1)^m ≤ ((l:ℝ) + 1)^m := pow_le_pow_left₀ hl1.le (by linarith) m
    have : 4^(m+1) * ((l:ℝ)-1)^m ≤ 4^(m+1) * ((l:ℝ)+1)^m := mul_le_mul_of_nonneg_left hmono (by positivity)
    rw [← add_div, div_le_div_iff₀ (by positivity) hf]
    nlinarith [hf]

lemma sep_q (K j : ℕ) (hK : 2 ≤ K) (hj : 2 ≤ j) :
    HasSeparatedBound j (Set.Icc (-(1/2)) (1/2)) (dividedDifference (q K) j)
      (16^j * (K:ℝ)^(j-1) / (j.factorial : ℝ)) := by
  have hsum := sep_sum K (fun l _ => sep_smul (cJ K l) (sepQ j l (by omega)))
  have hcongr := sep_congr hsum (fun x _ => DD_q K j (by omega) x)
  refine sep_mono hcongr ?_
  have hf : (0:ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hKr : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hterm : ∀ l ∈ Finset.range K, |cJ K l| * bQ j l ≤ 2^(3*j+1) * (K:ℝ)^(j-2) / (j.factorial : ℝ) := by
    intro l hl
    rw [Finset.mem_range] at hl
    by_cases h0 : l = 0
    · subst h0; simp only [cJ, if_true, abs_zero, zero_mul]; positivity
    · have hl1 : (1:ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
      have hc : |cJ K l| ≤ 4 / l := by
        unfold cJ; rw [if_neg h0]; exact OTDJackson.coef_bound K hK l h0
      have hb := bQ_le j l (by omega) (by omega)
      have hb0 : 0 ≤ bQ j l := by
        unfold bQ; rw [if_neg h0]; split_ifs
        · positivity
        · have : (0:ℝ) < (l:ℝ) - 1 := by
            have : (2:ℝ) ≤ l := by exact_mod_cast (by omega : 2 ≤ l)
            linarith
          positivity
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
      simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega] at hb ⊢
      have hl2 : ((l:ℝ) + 1) ≤ 2 * l := by linarith
      have hlK : (l:ℝ) ≤ K := by exact_mod_cast hl.le
      calc |cJ K l| * bQ (m+2) l ≤ (4 / l) * (4^(m+2) * ((l:ℝ) + 1)^(m+1) / ((m+2).factorial : ℝ)) :=
            mul_le_mul hc hb hb0 (by positivity)
        _ ≤ (4 / l) * (4^(m+2) * (2 * (l:ℝ))^(m+1) / ((m+2).factorial : ℝ)) := by
            gcongr
        _ = 2^(3*(m+2)+1) * (l:ℝ)^m / ((m+2).factorial : ℝ) := by
            field_simp
            rw [mul_pow, show (4:ℝ) = 2^2 by norm_num, ← pow_mul, pow_succ (l:ℝ) m]
            ring_nf
        _ ≤ 2^(3*(m+2)+1) * (K:ℝ)^m / ((m+2).factorial : ℝ) := by
            gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hf]
  have h16 : (2:ℝ)^(3*(m+2)+1) ≤ 16^(m+2) := by
    rw [show (16:ℝ) = 2^4 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc (K:ℝ) * (2^(3*(m+2)+1) * (K:ℝ)^m) = 2^(3*(m+2)+1) * (K:ℝ)^(m+1) := by rw [pow_succ]; ring
    _ ≤ 16^(m+2) * (K:ℝ)^(m+1) := mul_le_mul_of_nonneg_right h16 (by positivity)

section extras
variable {d : ℕ}
lemma quad_le_opNorm (A : Mat d) (x : Fin d → ℂ) :
    |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ opNorm A * (star x ⬝ᵥ x).re := by
  have := ContinuousLinearMap.rayleighQuotient_le_norm (Matrix.toEuclideanCLM (𝕜 := ℂ) A)
    (WithLp.toLp 2 x)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] at this
  rw [inner_eq', normsq_eq] at this
  simp only [WithLp.ofLp_toLp] at this
  rcases eq_or_lt_of_le (show 0 ≤ (star x ⬝ᵥ x).re from by
      rw [sum_normsq]; simp only [Complex.re_sum, Complex.ofReal_re]; positivity) with h0 | hpos
  · have hx : x = 0 := by
      have := (h0.symm)
      rw [sum_normsq] at this
      simp only [Complex.re_sum, Complex.ofReal_re] at this
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x i‖)).mp this
      funext i; have := h2 i (Finset.mem_univ i); simpa using this
    subst hx; simp
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at this
    exact this


lemma re_nonneg_of_psd {A : Mat d} (hA : A.PosSemidef) (x : Fin d → ℂ) :
    0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1

/-- sandwich: |quad Y| ≤ quad X -/
lemma opNorm_mul_le (A B : Mat d) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  unfold opNorm; rw [map_mul]; exact norm_mul_le _ _

lemma opNorm_conj (A : Mat d) : opNorm Aᴴ = opNorm A := by
  unfold opNorm
  rw [← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint.norm_map _

lemma opNorm_QXQ {d : ℕ} {Q : Mat d} (hQH : Qᴴ = Q) (hQ : Q * Q = Q) (X : Mat d) :
    opNorm (Q * X * Q) ≤ opNorm X := by
  have hQ1 : opNorm Q ≤ 1 := by
    have hQpsd : Q.PosSemidef := by
      have := Matrix.posSemidef_conjTranspose_mul_self Q; rwa [hQH, hQ] at this
    have h1Q : (1 - Q).PosSemidef := by
      have := Matrix.posSemidef_conjTranspose_mul_self (1 - Q)
      have e : (1 - Q)ᴴ * (1 - Q) = 1 - Q := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQH, Matrix.sub_mul, Matrix.mul_sub,
          Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hQ]; abel
      rwa [e] at this
    refine opNorm_le_of_quad hQpsd.1 zero_le_one (fun x => ?_)
    have h1 := re_nonneg_of_psd hQpsd x
    have h2 := re_nonneg_of_psd h1Q x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at h2
    rw [abs_of_nonneg h1, one_mul]; linarith
  have hX0 := opNorm_nonneg' X
  have hQ0 := opNorm_nonneg' Q
  calc opNorm (Q * X * Q) ≤ opNorm Q * opNorm X * opNorm Q :=
        (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg' _))
    _ ≤ opNorm X := by nlinarith [mul_le_mul_of_nonneg_right hQ1 hX0]


lemma eig_abs_le {Y : Mat d} (hY : Y.IsHermitian) (a : Fin d) : |hY.eigenvalues a| ≤ opNorm Y := by
  set v := hY.eigenvectorBasis a
  have hv := hY.mulVec_eigenvectorBasis a
  have h1 := quad_le_opNorm Y (⇑v)
  have hn : (star (⇑v) ⬝ᵥ (⇑v : Fin d → ℂ)).re = 1 := by
    have := normsq_eq v
    rw [hY.eigenvectorBasis.orthonormal.1 a] at this
    simpa using this.symm
  rw [hv, dotProduct_smul, hn, mul_one] at h1
  have : (hY.eigenvalues a • (star (⇑v) ⬝ᵥ (⇑v : Fin d → ℂ))).re = hY.eigenvalues a := by
    rw [Complex.real_smul, Complex.re_ofReal_mul, hn, mul_one]
  rwa [this] at h1

lemma opNorm_le_trace {S : Mat d} (hS : S.PosSemidef) : opNorm S ≤ (S.trace).re := by
  have hH := hS.1
  have htr0 : 0 ≤ (S.trace).re := (Complex.nonneg_iff.1 hS.trace_nonneg).1
  refine opNorm_le_of_quad hH htr0 (fun x => ?_)
  have hid : cfc (fun t : ℝ => t) S = S := cfc_id' ℝ S hH.isSelfAdjoint
  have hq := quad_cfc hH (fun t => t) x
  rw [hid] at hq
  rw [hq]
  set y := star (hH.eigenvectorUnitary : Mat d) *ᵥ x
  have hyy : (star x ⬝ᵥ x) = star y ⬝ᵥ y := (unitary_norm _ (U_mem hH) x).symm
  rw [hyy, sum_normsq y]
  simp only [Complex.re_sum, Complex.ofReal_re]
  have h1 : ∀ i, (((hH.eigenvalues i : ℝ) : ℂ) * (star (y i) * y i)).re = hH.eigenvalues i * ‖y i‖^2 := by
    intro i
    have : star (y i) * y i = ((‖y i‖^2 : ℝ) : ℂ) := by
      rw [mul_comm]; show y i * (starRingEnd ℂ) (y i) = _
      rw [Complex.mul_conj', Complex.ofReal_pow]
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [h1]
  have hl0 : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hS.eigenvalues_nonneg i
  have htr : (S.trace).re = ∑ i, hH.eigenvalues i := by rw [hH.trace_eq_sum_eigenvalues]; simp
  have hle : ∀ i, hH.eigenvalues i ≤ (S.trace).re := fun i => by
    rw [htr]; exact Finset.single_le_sum (fun j _ => hl0 j) (Finset.mem_univ i)
  rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hl0 i) (sq_nonneg _))), Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _))

end extras

lemma foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => by simp
  | (b :: l), a => by
    have ih := foldl_max_ge l (max a b)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨le_trans (le_max_left a b) ih.1, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · exact le_trans (le_max_right a x) ih.1
    · exact ih.2 x hx

lemma foldl_max_le : ∀ (l : List ℕ) (a b : ℕ), a ≤ b → (∀ x ∈ l, x ≤ b) → l.foldl max a ≤ b
  | [], a, b, h, _ => by simpa using h
  | (c :: l), a, b, h, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le l _ b (max_le h (hl c (by simp))) (fun x hx => hl x (by simp [hx]))


lemma deg_univariate {d : ℕ} (K : ℕ) (hK : 2 ≤ K) : expressionDegree (univariate d K) ≤ K := by
  unfold expressionDegree
  refine foldl_max_le _ 0 K (Nat.zero_le _) (fun x hx => ?_)
  rw [List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  rw [univariate_words, List.mem_map] at hw
  obtain ⟨k, hk, rfl⟩ := hw
  simp only [List.length_replicate]
  rw [Finset.mem_toList] at hk
  exact (Polynomial.le_natDegree_of_mem_supp k hk).trans (lemma_2_3 K hK).1

lemma real_univariate {d : ℕ} (K : ℕ) : realOnHermitian (univariate d K) := by
  intro X Y hX hY
  unfold evaluate
  rw [univariate_words, List.map_map]
  have hc : (univariate d K).constant = 0 := rfl
  rw [hc, zero_add]
  have : ∀ k : ℕ, ((fun w => (wordEval w X Y).trace) ∘ (fun k => (⟨List.replicate k ((1 : Mat d), true),
      (((q K).coeff k : ℝ) : ℂ) • 1⟩ : Word d))) k = (((q K).coeff k : ℝ) : ℂ) * (Y ^ k).trace := by
    intro k
    simp only [Function.comp_apply, wordEval, List.map_replicate, List.prod_replicate, if_true, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  rw [List.map_congr_left (fun k _ => this k), Finset.sum_map_toList]
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [Complex.im_ofReal_mul]
  have hYk : (Y ^ k).IsHermitian := hY.pow k
  have : star (Y ^ k).trace = (Y ^ k).trace := by rw [← Matrix.trace_conjTranspose, hYk.eq]
  rw [Complex.conj_eq_iff_im.1 this, mul_zero]

end OTDUni


open scoped ComplexOrder
namespace OTDB2
open Matrix OptimalTraceDistance.Estimation

variable {d : ℕ}

lemma opNorm_nonneg' (A : Mat d) : 0 ≤ opNorm A := norm_nonneg _
lemma opNorm_mul_le (A B : Mat d) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  unfold opNorm; rw [map_mul]; exact norm_mul_le _ _
lemma opNorm_one_le : opNorm (1 : Mat d) ≤ 1 := by
  unfold opNorm; rw [map_one]; exact ContinuousLinearMap.norm_id_le

/-! ### monomials in the perturbations -/

inductive Fac (d : ℕ)
  | const : Mat d → Fac d
  | e0 : Fac d
  | e1 : Fac d

def Fac.val (E₀ E₁ : Mat d) : Fac d → Mat d
  | .const A => A
  | .e0 => E₀
  | .e1 => E₁

def Fac.nb : Fac d → ℝ
  | .const A => opNorm A
  | .e0 => 1
  | .e1 => 1

def Fac.deg : Fac d → ℕ
  | .const _ => 0
  | .e0 => 1
  | .e1 => 1

def mval (E₀ E₁ : Mat d) (w : List (Fac d)) : Mat d := (w.map (Fac.val E₀ E₁)).prod
def mnb (w : List (Fac d)) : ℝ := (w.map Fac.nb).prod
def mdeg (w : List (Fac d)) : ℕ := (w.map Fac.deg).sum

lemma Fac.nb_nonneg (f : Fac d) : 0 ≤ f.nb := by
  cases f <;> simp [Fac.nb, opNorm_nonneg']

lemma mnb_nonneg (w : List (Fac d)) : 0 ≤ mnb w := by
  unfold mnb
  induction w with
  | nil => simp
  | cons f w ih => simp only [List.map_cons, List.prod_cons]; exact mul_nonneg f.nb_nonneg ih

lemma mval_append (E₀ E₁ : Mat d) (u v : List (Fac d)) :
    mval E₀ E₁ (u ++ v) = mval E₀ E₁ u * mval E₀ E₁ v := by simp [mval]
lemma mnb_append (u v : List (Fac d)) : mnb (u ++ v) = mnb u * mnb v := by simp [mnb]
lemma mdeg_append (u v : List (Fac d)) : mdeg (u ++ v) = mdeg u + mdeg v := by simp [mdeg]

/-- matrix-valued ordered representation of order `j` with bound `M` -/
def MOR (j : ℕ) (Ψ : Mat d → Mat d → Mat d) (M : ℝ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → List (Fac d)),
    (∀ i, mdeg (w i) = j) ∧ (∀ E₀ E₁, Ψ E₀ E₁ = ∑ i, c i • mval E₀ E₁ (w i)) ∧
    ∑ i, ‖c i‖ * mnb (w i) ≤ M

lemma mor_congr {j : ℕ} {Ψ Φ : Mat d → Mat d → Mat d} {M : ℝ} (h : ∀ E₀ E₁, Ψ E₀ E₁ = Φ E₀ E₁)
    (hΨ : MOR j Ψ M) : MOR j Φ M := by
  obtain ⟨n, c, w, hd, hid, hb⟩ := hΨ
  exact ⟨n, c, w, hd, fun E₀ E₁ => (h E₀ E₁).symm.trans (hid E₀ E₁), hb⟩

lemma mor_mono {j : ℕ} {Ψ : Mat d → Mat d → Mat d} {M M' : ℝ} (hΨ : MOR j Ψ M) (h : M ≤ M') :
    MOR j Ψ M' := by
  obtain ⟨n, c, w, hd, hid, hb⟩ := hΨ
  exact ⟨n, c, w, hd, hid, hb.trans h⟩

lemma mor_zero (j : ℕ) : MOR j (fun _ _ : Mat d => (0 : Mat d)) 0 :=
  ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun _ _ => by simp, by simp⟩

lemma mor_single {j : ℕ} (w : List (Fac d)) (hw : mdeg w = j) :
    MOR j (fun E₀ E₁ => mval E₀ E₁ w) (mnb w) :=
  ⟨1, fun _ => 1, fun _ => w, fun _ => hw, fun _ _ => by simp, by simp⟩

lemma mor_const (A : Mat d) : MOR 0 (fun _ _ => A) (opNorm A) := by
  have := mor_single (j := 0) [Fac.const A] (by simp [mdeg, Fac.deg])
  simpa [mval, mnb, Fac.val, Fac.nb] using this

lemma mor_e0 : MOR (d := d) 1 (fun E₀ _ => E₀) (1 : ℝ) := by
  have := mor_single (j := 1) [(Fac.e0 : Fac d)] (by simp [mdeg, Fac.deg])
  simpa [mval, mnb, Fac.val, Fac.nb] using this

lemma mor_e1 : MOR (d := d) 1 (fun _ E₁ => E₁) (1 : ℝ) := by
  have := mor_single (j := 1) [(Fac.e1 : Fac d)] (by simp [mdeg, Fac.deg])
  simpa [mval, mnb, Fac.val, Fac.nb] using this

lemma mor_add {j : ℕ} {Ψ₁ Ψ₂ : Mat d → Mat d → Mat d} {M₁ M₂ : ℝ}
    (h₁ : MOR j Ψ₁ M₁) (h₂ : MOR j Ψ₂ M₂) :
    MOR j (fun E₀ E₁ => Ψ₁ E₀ E₁ + Ψ₂ E₀ E₁) (M₁ + M₂) := by
  obtain ⟨n₁, c₁, w₁, hd₁, hid₁, hb₁⟩ := h₁
  obtain ⟨n₂, c₂, w₂, hd₂, hid₂, hb₂⟩ := h₂
  refine ⟨n₁ + n₂, Fin.append c₁ c₂, Fin.append w₁ w₂, fun i => ?_, fun E₀ E₁ => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hd₁, hd₂]
  · dsimp only; rw [hid₁, hid₂, Fin.sum_univ_add]; simp
  · rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right]; linarith

lemma mor_smul {j : ℕ} {Ψ : Mat d → Mat d → Mat d} {M : ℝ} (a : ℂ) (h : MOR j Ψ M) :
    MOR j (fun E₀ E₁ => a • Ψ E₀ E₁) (‖a‖ * M) := by
  obtain ⟨n, c, w, hd, hid, hb⟩ := h
  refine ⟨n, fun i => a * c i, w, hd, fun E₀ E₁ => ?_, ?_⟩
  · dsimp only; rw [hid, Finset.smul_sum]; simp only [smul_smul]
  · simp only [norm_mul, mul_assoc]; rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

lemma mor_sum {j : ℕ} {ι : Type*} (S : Finset ι) {Ψ : ι → Mat d → Mat d → Mat d} {M : ι → ℝ}
    (h : ∀ i ∈ S, MOR j (Ψ i) (M i)) :
    MOR j (fun E₀ E₁ => ∑ i ∈ S, Ψ i E₀ E₁) (∑ i ∈ S, M i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using mor_zero (d := d) j
  | insert a S ha ih =>
    have := mor_add (h a (Finset.mem_insert_self a S)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    refine mor_congr (fun E₀ E₁ => ?_) (mor_mono this (le_of_eq ?_))
    · rw [Finset.sum_insert ha]
    · rw [Finset.sum_insert ha]

lemma mor_mul {j k : ℕ} {Ψ Φ : Mat d → Mat d → Mat d} {M N : ℝ}
    (hΨ : MOR j Ψ M) (hΦ : MOR k Φ N) :
    MOR (j + k) (fun E₀ E₁ => Ψ E₀ E₁ * Φ E₀ E₁) (M * N) := by
  obtain ⟨n₁, c₁, w₁, hd₁, hid₁, hb₁⟩ := hΨ
  obtain ⟨n₂, c₂, w₂, hd₂, hid₂, hb₂⟩ := hΦ
  set e := finProdFinEquiv (m := n₁) (n := n₂)
  refine ⟨n₁ * n₂, fun i => c₁ (e.symm i).1 * c₂ (e.symm i).2,
    fun i => w₁ (e.symm i).1 ++ w₂ (e.symm i).2, fun i => ?_, fun E₀ E₁ => ?_, ?_⟩
  · rw [mdeg_append, hd₁, hd₂]
  · dsimp only
    rw [hid₁, hid₂, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv e _ _ (fun p => ?_)
    simp only [Equiv.symm_apply_apply]
    rw [mval_append, smul_mul_smul_comm]
  · have h0 : 0 ≤ ∑ i, ‖c₂ i‖ * mnb (w₂ i) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (mnb_nonneg _))
    have hM : 0 ≤ M := le_trans (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (norm_nonneg _) (mnb_nonneg _))) hb₁
    calc ∑ i, ‖c₁ (e.symm i).1 * c₂ (e.symm i).2‖ * mnb (w₁ (e.symm i).1 ++ w₂ (e.symm i).2)
        = ∑ p : Fin n₁ × Fin n₂, (‖c₁ p.1‖ * mnb (w₁ p.1)) * (‖c₂ p.2‖ * mnb (w₂ p.2)) := by
          rw [← e.sum_comp]
          refine Fintype.sum_congr _ _ (fun p => ?_)
          simp only [Equiv.symm_apply_apply, norm_mul, mnb_append]; ring
      _ = (∑ i, ‖c₁ i‖ * mnb (w₁ i)) * (∑ i, ‖c₂ i‖ * mnb (w₂ i)) := by
          rw [Finset.sum_mul_sum, ← Finset.sum_product']; rfl
      _ ≤ M * N := mul_le_mul hb₁ hb₂ h0 hM

/-! ### normal form and conversion to ordered bounds -/

def evE (E₀ E₁ : Mat d) (t : Bool) : Mat d := if t then E₁ else E₀

lemma mdeg_const (A : Mat d) (l : List (Fac d)) : mdeg (Fac.const A :: l) = mdeg l := by
  simp [mdeg, Fac.deg]

def nfAux : List (Fac d) → List (Mat d × Bool) × Mat d
  | [] => ([], 1)
  | (Fac.const A) :: l =>
      match (nfAux l).1 with
      | [] => ([], A * (nfAux l).2)
      | (B, t) :: ps => ((A * B, t) :: ps, (nfAux l).2)
  | Fac.e0 :: l => ((1, false) :: (nfAux l).1, (nfAux l).2)
  | Fac.e1 :: l => ((1, true) :: (nfAux l).1, (nfAux l).2)

def nfval (E₀ E₁ : Mat d) (p : List (Mat d × Bool) × Mat d) : Mat d :=
  (p.1.map (fun At => At.1 * evE E₀ E₁ At.2)).prod * p.2

def nfnb (p : List (Mat d × Bool) × Mat d) : ℝ := (p.1.map (fun At => opNorm At.1)).prod * opNorm p.2

lemma nf_facts (E₀ E₁ : Mat d) : ∀ w : List (Fac d),
    nfval E₀ E₁ (nfAux w) = mval E₀ E₁ w ∧ (nfAux w).1.length = mdeg w ∧ nfnb (nfAux w) ≤ mnb w
  | [] => by
    refine ⟨by simp [nfval, nfAux, mval], by simp [nfAux, mdeg], ?_⟩
    simp only [nfnb, nfAux, List.map_nil, List.prod_nil, one_mul, mnb]; exact opNorm_one_le
  | (Fac.const A) :: l => by
    obtain ⟨h1, h2, h3⟩ := nf_facts E₀ E₁ l
    unfold nfAux
    rcases hps : (nfAux l).1 with _ | ⟨⟨B, t⟩, ps⟩
    · simp only [nfval, nfnb, List.map_nil, List.prod_nil, one_mul, List.length_nil]
      simp only [nfval, hps, List.map_nil, List.prod_nil, one_mul] at h1
      simp only [hps, List.length_nil] at h2
      simp only [nfnb, hps, List.map_nil, List.prod_nil, one_mul] at h3
      refine ⟨by simp [mval, h1, Fac.val], by rw [mdeg_const, ← h2], ?_⟩
      simp only [mnb, List.map_cons, List.prod_cons, Fac.nb]
      refine (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (opNorm_nonneg' _))
      exact h3
    · simp only [nfval, hps, List.map_cons, List.prod_cons] at h1
      simp only [hps, List.length_cons] at h2
      simp only [nfnb, hps, List.map_cons, List.prod_cons] at h3
      refine ⟨?_, ?_, ?_⟩
      · simp only [nfval, List.map_cons, List.prod_cons, mval, Fac.val]
        rw [← mval, ← h1]; simp only [Matrix.mul_assoc]
      · rw [mdeg_const, ← h2]; simp
      · simp only [nfnb, List.map_cons, List.prod_cons, mnb, Fac.nb]
        have hp0 : 0 ≤ (ps.map (fun At => opNorm At.1)).prod * opNorm (nfAux l).2 := by
          refine mul_nonneg (List.prod_nonneg (fun x hx => ?_)) (opNorm_nonneg' _)
          obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact opNorm_nonneg' _
        calc opNorm (A * B) * (ps.map (fun At => opNorm At.1)).prod * opNorm (nfAux l).2
            = opNorm (A * B) * ((ps.map (fun At => opNorm At.1)).prod * opNorm (nfAux l).2) := by ring
          _ ≤ opNorm A * opNorm B * ((ps.map (fun At => opNorm At.1)).prod * opNorm (nfAux l).2) :=
              mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) hp0
          _ = opNorm A * (opNorm B * (ps.map (fun At => opNorm At.1)).prod * opNorm (nfAux l).2) := by
              ring
          _ ≤ opNorm A * mnb l := by
              refine mul_le_mul_of_nonneg_left ?_ (opNorm_nonneg' _)
              exact h3
  | Fac.e0 :: l => by
    obtain ⟨h1, h2, h3⟩ := nf_facts E₀ E₁ l
    refine ⟨?_, ?_, ?_⟩
    · simp only [nfval, nfAux, List.map_cons, List.prod_cons, mval, Fac.val, evE] at h1 ⊢
      rw [Matrix.one_mul, Matrix.mul_assoc, h1]; simp
    · simp [nfAux, mdeg, Fac.deg, h2]; ring
    · simp only [nfnb, nfAux, List.map_cons, List.prod_cons, mnb, Fac.nb, one_mul] at h3 ⊢
      rw [mul_assoc]
      calc opNorm (1 : Mat d) * ((List.map (fun At => opNorm At.1) (nfAux l).1).prod * opNorm (nfAux l).2)
          ≤ 1 * ((List.map (fun At => opNorm At.1) (nfAux l).1).prod * opNorm (nfAux l).2) := by
            refine mul_le_mul_of_nonneg_right opNorm_one_le ?_
            refine mul_nonneg (List.prod_nonneg (fun x hx => ?_)) (opNorm_nonneg' _)
            obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact opNorm_nonneg' _
        _ ≤ _ := by rw [one_mul]; exact h3
  | Fac.e1 :: l => by
    obtain ⟨h1, h2, h3⟩ := nf_facts E₀ E₁ l
    refine ⟨?_, ?_, ?_⟩
    · simp only [nfval, nfAux, List.map_cons, List.prod_cons, mval, Fac.val, evE] at h1 ⊢
      rw [Matrix.one_mul, Matrix.mul_assoc, h1]; simp
    · simp [nfAux, mdeg, Fac.deg, h2]; ring
    · simp only [nfnb, nfAux, List.map_cons, List.prod_cons, mnb, Fac.nb, one_mul] at h3 ⊢
      rw [mul_assoc]
      calc opNorm (1 : Mat d) * ((List.map (fun At => opNorm At.1) (nfAux l).1).prod * opNorm (nfAux l).2)
          ≤ 1 * ((List.map (fun At => opNorm At.1) (nfAux l).1).prod * opNorm (nfAux l).2) := by
            refine mul_le_mul_of_nonneg_right opNorm_one_le ?_
            refine mul_nonneg (List.prod_nonneg (fun x hx => ?_)) (opNorm_nonneg' _)
            obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact opNorm_nonneg' _
        _ ≤ _ := by rw [one_mul]; exact h3

lemma list_to_fin : ∀ (ps : List (Mat d × Bool)) (L : Mat d) (j : ℕ), ps.length = j →
    ∃ (A : Fin (j+1) → Mat d) (t : Fin j → Bool),
      (∀ E₀ E₁ : Mat d, (List.ofFn (fun k : Fin j => A k.castSucc * (if t k then E₁ else E₀))).prod *
          A (Fin.last j) = (ps.map (fun At => At.1 * evE E₀ E₁ At.2)).prod * L) ∧
      ∏ k, opNorm (A k) = (ps.map (fun At => opNorm At.1)).prod * opNorm L
  | [], L, j, h => by
    subst h
    exact ⟨fun _ => L, Fin.elim0, fun _ _ => by simp, by simp⟩
  | (B, s) :: ps, L, j, h => by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨ps.length, by simp at h; omega⟩
    obtain ⟨A', t', hid, hnb⟩ := list_to_fin ps L j' (by simpa using h)
    refine ⟨Fin.cons B A', Fin.cons s t', fun E₀ E₁ => ?_, ?_⟩
    · rw [List.ofFn_succ, List.prod_cons]
      simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ]
      have hl : (Fin.last (j'+1) : Fin (j'+2)) = (Fin.last j').succ := rfl
      rw [hl, Fin.cons_succ]
      have e : ∀ k : Fin j', (Fin.cons B A' : Fin (j'+2) → Mat d) k.succ.castSucc = A' k.castSucc := by
        intro k; rw [← Fin.succ_castSucc, Fin.cons_succ]
      simp only [e]
      rw [Matrix.mul_assoc, hid]
      simp [evE, Matrix.mul_assoc]
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hnb, List.map_cons, List.prod_cons]; ring

theorem mor_trace {j : ℕ} {Ψ : Mat d → Mat d → Mat d} {M : ℝ} (h : MOR j Ψ M) :
    HasOrderedBound j (fun E₀ E₁ => (Ψ E₀ E₁).trace) M := by
  obtain ⟨n, c, w, hd, hid, hb⟩ := h
  have hconv : ∀ i, ∃ (A : Fin (j+1) → Mat d) (t : Fin j → Bool),
      (∀ E₀ E₁ : Mat d, (List.ofFn (fun k : Fin j => A k.castSucc * (if t k then E₁ else E₀))).prod *
          A (Fin.last j) = mval E₀ E₁ (w i)) ∧ ∏ k, opNorm (A k) ≤ mnb (w i) := by
    intro i
    have hf := nf_facts (0 : Mat d) 0 (w i)
    obtain ⟨A, t, hA, hn⟩ := list_to_fin (nfAux (w i)).1 (nfAux (w i)).2 j (by rw [hf.2.1, hd i])
    refine ⟨A, t, fun E₀ E₁ => ?_, ?_⟩
    · rw [hA]; exact (nf_facts E₀ E₁ (w i)).1
    · rw [hn]; exact hf.2.2
  choose A t hA hn using hconv
  refine ⟨n, c, A, t, fun E₀ E₁ => ?_, ?_⟩
  · dsimp only
    rw [hid, Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.trace_smul, hA, smul_eq_mul]
  · refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) hb
    exact mul_le_mul_of_nonneg_left (hn i) (norm_nonneg _)


def trP (P : Polynomial (Mat d)) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff k).trace * Polynomial.X ^ k

lemma trP_coeff (P : Polynomial (Mat d)) (j : ℕ) : (trP P).coeff j = (P.coeff j).trace := by
  unfold trP
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Matrix.trace_zero]

lemma eval_central_mul (P Q : Polynomial (Mat d)) (z : ℂ) :
    (P * Q).eval (z • (1 : Mat d)) = P.eval (z • 1) * Q.eval (z • 1) :=
  Polynomial.eval₂_mul_noncomm _ _ (fun k => (Commute.one_right _).smul_right z)

lemma eval_central_list (l : List (Polynomial (Mat d))) (z : ℂ) :
    l.prod.eval (z • (1 : Mat d)) = (l.map (fun P => P.eval (z • 1))).prod := by
  induction l with
  | nil => simp
  | cons P l ih => rw [List.prod_cons, eval_central_mul, ih]; simp

lemma trP_eval (P : Polynomial (Mat d)) (z : ℂ) :
    (trP P).eval z = (P.eval (z • (1 : Mat d))).trace := by
  conv_rhs => rw [Polynomial.eval_eq_sum_range, Matrix.trace_sum]
  unfold trP
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, smul_pow,
    one_pow, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, mul_comm]

lemma wordLine_eval (w : Word d) (X Y E₀ E₁ : Mat d) (z : ℂ) :
    (wordLine w X Y E₀ E₁).eval (z • (1 : Mat d)) = wordEval w (X + z • E₀) (Y + z • E₁) := by
  unfold wordLine wordEval
  rw [eval_central_mul, eval_central_list, List.map_map, Polynomial.eval_C]
  congr 2
  refine List.map_congr_left (fun At _ => ?_)
  simp only [Function.comp_apply, eval_central_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X]
  rw [Matrix.smul_mul, Matrix.one_mul]
  cases At.2 <;> simp

def tpoly (f : TraceExpression d) (X Y E₀ E₁ : Mat d) : Polynomial ℂ :=
  Polynomial.C f.constant + (f.words.map (fun w => trP (wordLine w X Y E₀ E₁))).sum

lemma tpoly_coeff (f : TraceExpression d) (X Y E₀ E₁ : Mat d) (j : ℕ) :
    (tpoly f X Y E₀ E₁).coeff j = taylor f X Y j E₀ E₁ := by
  unfold tpoly taylor
  rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_list_sum, List.map_map]
  congr 2
  refine List.map_congr_left (fun w _ => ?_)
  simp [trP_coeff]

lemma tpoly_eval (f : TraceExpression d) (X Y E₀ E₁ : Mat d) (z : ℂ) :
    (tpoly f X Y E₀ E₁).eval z = evaluate f (X + z • E₀) (Y + z • E₁) := by
  unfold tpoly evaluate
  rw [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_listSum, List.map_map]
  congr 2
  refine List.map_congr_left (fun w _ => ?_)
  simp [trP_eval, wordLine_eval]

theorem taylor_lin {ι : Type*} (S : Finset ι) (f : TraceExpression d) (g : ι → TraceExpression d)
    (c : ι → ℂ) (h : ∀ X Y, evaluate f X Y = ∑ i ∈ S, c i * evaluate (g i) X Y)
    (X Y : Mat d) (j : ℕ) (E₀ E₁ : Mat d) :
    taylor f X Y j E₀ E₁ = ∑ i ∈ S, c i * taylor (g i) X Y j E₀ E₁ := by
  have hp : tpoly f X Y E₀ E₁ = ∑ i ∈ S, Polynomial.C (c i) * tpoly (g i) X Y E₀ E₁ := by
    refine Polynomial.funext (fun z => ?_)
    rw [tpoly_eval, h, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, tpoly_eval]
  rw [← tpoly_coeff, hp, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.coeff_C_mul, tpoly_coeff]


def varOf (X Y : Mat d) (t : Bool) : Mat d := if t then Y else X

def exprEval (u : MatrixExpression d) (X Y : Mat d) : Mat d :=
  (u.map (fun w => wordEval w X Y)).sum

lemma wordEval_mul (u v : Word d) (X Y : Mat d) :
    wordEval (wordMul u v) X Y = wordEval u X Y * wordEval v X Y := by
  unfold wordMul
  rcases v with ⟨vf, vt⟩
  cases vf with
  | nil => simp [wordEval, Matrix.mul_assoc]
  | cons At xs =>
    rcases At with ⟨A, t⟩
    simp only [wordEval, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    simp only [Matrix.mul_assoc]

lemma exprEval_append (u v : MatrixExpression d) (X Y : Mat d) :
    exprEval (u ++ v) X Y = exprEval u X Y + exprEval v X Y := by
  simp [exprEval]

lemma exprEval_mul (u v : MatrixExpression d) (X Y : Mat d) :
    exprEval (exprMul u v) X Y = exprEval u X Y * exprEval v X Y := by
  unfold exprMul exprEval
  induction u with
  | nil => simp
  | cons a u ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      Matrix.add_mul]
    rw [ih]; congr 1
    rw [List.map_map]
    simp only [Function.comp_def, wordEval_mul]
    rw [← List.sum_map_mul_left]

lemma exprEval_const (A : Mat d) (X Y : Mat d) : exprEval (exprConst A) X Y = A := by
  simp [exprEval, exprConst, wordEval]

lemma exprEval_var (t : Bool) (X Y : Mat d) : exprEval (exprVar d t) X Y = varOf X Y t := by
  simp [exprEval, exprVar, wordEval, varOf]

lemma exprEval_scale (c : ℝ) (u : MatrixExpression d) (X Y : Mat d) :
    exprEval (exprScale c u) X Y = (c : ℂ) • exprEval u X Y := by
  unfold exprScale exprEval
  induction u with
  | nil => simp
  | cons a u ih =>
    simp only [List.map_cons, List.sum_cons, List.map_map, smul_add] at ih ⊢
    rw [← ih]
    simp [wordEval, Function.comp_def]

lemma exprEval_pow (u : MatrixExpression d) (X Y : Mat d) (k : ℕ) :
    exprEval (exprPow u k) X Y = exprEval u X Y ^ k := by
  induction k with
  | zero => simp [exprPow, exprEval_const]
  | succ k ih => rw [exprPow, exprEval_mul, ih, pow_succ]

lemma exprEval_flatMap {α : Type*} (l : List α) (g : α → MatrixExpression d) (X Y : Mat d) :
    exprEval (l.flatMap g) X Y = (l.map (fun k => exprEval (g k) X Y)).sum := by
  induction l with
  | nil => simp [exprEval]
  | cons k l ih => simp only [List.flatMap_cons, List.map_cons, List.sum_cons, exprEval_append, ih]

lemma exprEval_poly (p : Polynomial ℝ) (u : MatrixExpression d) (X Y : Mat d) :
    exprEval (exprPoly p u) X Y = matrixEval p (exprEval u X Y) := by
  unfold exprPoly matrixEval
  rw [exprEval_flatMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [exprEval_scale, exprEval_pow]

lemma evaluate_traceExpr (u : MatrixExpression d) (X Y : Mat d) :
    evaluate (traceExpr u) X Y = (exprEval u X Y).trace := by
  simp only [evaluate, traceExpr, exprEval, zero_add]
  rw [Matrix.trace_list_sum, List.map_map]; rfl



lemma matrixEval_eq_aeval (p : Polynomial ℝ) (B : Mat d) : matrixEval p B = Polynomial.aeval B p := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, matrixEval, Polynomial.sum_def]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [show ((p.coeff k : ℝ) : ℂ) • B ^ k = (p.coeff k : ℝ) • B ^ k from
    (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm]


/-! ### polynomial tools -/

def G (K : ℕ) (b s : ℝ) : TraceExpression d :=
  let r := exprPoly (filter b) (exprVar d false)
  traceExpr (exprPoly (qScaled K s) (exprMul (exprMul r (exprVar d true)) r))

lemma eval_G (K : ℕ) (b s : ℝ) (X Y : Mat d) :
    evaluate (G K b s) X Y = (matrixEval (qScaled K s)
      (matrixEval (filter b) X * Y * matrixEval (filter b) X)).trace := by
  simp only [G, evaluate_traceExpr, exprEval_poly, exprEval_mul, exprEval_var, varOf]
  rfl

def peval (p : Polynomial ℝ) (P : Polynomial (Mat d)) : Polynomial (Mat d) :=
  ∑ k ∈ p.support, ((p.coeff k : ℝ) : ℂ) • P ^ k

lemma eval_central_pow (P : Polynomial (Mat d)) (z : ℂ) :
    ∀ k : ℕ, (P ^ k).eval (z • (1 : Mat d)) = (P.eval (z • 1)) ^ k
  | 0 => by simp
  | k+1 => by rw [pow_succ, eval_central_mul, eval_central_pow P z k, pow_succ]

lemma peval_eval (p : Polynomial ℝ) (P : Polynomial (Mat d)) (z : ℂ) :
    (peval p P).eval (z • (1 : Mat d)) = matrixEval p (P.eval (z • 1)) := by
  unfold peval matrixEval
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_smul, eval_central_pow]

def Lt (A E : Mat d) : Polynomial (Mat d) := Polynomial.C A + Polynomial.X * Polynomial.C E

lemma Lt_eval (A E : Mat d) (z : ℂ) : (Lt A E).eval (z • (1 : Mat d)) = A + z • E := by
  unfold Lt
  rw [Polynomial.eval_add, Polynomial.eval_C, eval_central_mul, Polynomial.eval_X, Polynomial.eval_C,
    Matrix.smul_mul, Matrix.one_mul]

def Rt (b : ℝ) (X E₀ : Mat d) : Polynomial (Mat d) := peval (filter b) (Lt X E₀)
def Zt (b : ℝ) (X Y E₀ E₁ : Mat d) : Polynomial (Mat d) := Rt b X E₀ * Lt Y E₁ * Rt b X E₀

theorem taylor_eq (K : ℕ) (b s : ℝ) (X Y : Mat d) (j : ℕ) (E₀ E₁ : Mat d) :
    taylor (G K b s) X Y j E₀ E₁ = ((peval (qScaled K s) (Zt b X Y E₀ E₁)).coeff j).trace := by
  rw [← tpoly_coeff, ← trP_coeff]
  congr 1
  refine Polynomial.funext (fun z => ?_)
  rw [tpoly_eval, trP_eval, peval_eval, eval_G]
  congr 2
  unfold Zt Rt
  rw [eval_central_mul, eval_central_mul, peval_eval, Lt_eval, Lt_eval]

/-! ### spectral expansion of a polynomial around a Hermitian matrix -/

lemma Lt_natDegree (A E : Mat d) : (Lt A E).natDegree ≤ 1 := by
  unfold Lt
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
  exact (Polynomial.natDegree_mul_le).trans (by rw [Polynomial.natDegree_C, add_zero]; exact Polynomial.natDegree_X_le)

lemma Pk_eq (Z E : Mat d) (k : ℕ) : OTDUni.Pk Z E k = (Lt Z E) ^ k := rfl

lemma Pk_coeff_zero (Z E : Mat d) : ∀ k, (OTDUni.Pk Z E k).coeff 0 = Z ^ k
  | 0 => by rw [OTDUni.Pk_zero]; simp
  | k+1 => by rw [OTDUni.Pk_coeff_succ_zero, Pk_coeff_zero Z E k, pow_succ']

lemma matrixEval_expand (p : Polynomial ℝ) (Z E : Mat d) :
    matrixEval p (Z + E) = ∑ a ∈ Finset.range (p.natDegree + 1),
      ∑ k ∈ p.support, ((p.coeff k : ℝ) : ℂ) • (OTDUni.Pk Z E k).coeff a := by
  rw [Finset.sum_comm]
  unfold matrixEval
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [← Finset.smul_sum]
  congr 1
  have hk' : k ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp k hk
  have hdeg : (OTDUni.Pk Z E k).natDegree < p.natDegree + 1 := by
    rw [Pk_eq]
    have := Polynomial.natDegree_pow_le (p := Lt Z E) (n := k)
    have h1 := Lt_natDegree Z E
    nlinarith
  have := Polynomial.eval_eq_sum_range' hdeg (1 : Mat d)
  simp only [one_pow, Matrix.mul_one] at this
  rw [← this]
  have h1 : (1 : Mat d) = (1:ℂ) • (1 : Mat d) := by simp
  rw [h1, Pk_eq, eval_central_pow, Lt_eval, one_smul]

/-- a separated representation of the divided difference gives a product representation -/
theorem coeff_rep (p : Polynomial ℝ) {Z : Mat d} (hZ : Z.IsHermitian) {I : Set ℝ}
    (hspec : ∀ i, hZ.eigenvalues i ∈ I) {a : ℕ} {M : ℝ}
    (hsep : HasSeparatedBound a I (dividedDifference p a) M) :
    ∃ (L : ℕ) (c : Fin L → ℝ) (Gm : Fin L → Fin (a+1) → Mat d),
      (∑ α, |c α| * ∏ i, opNorm (Gm α i)) ≤ M ∧
      ∀ E : Mat d, ∑ k ∈ p.support, ((p.coeff k : ℝ) : ℂ) • (OTDUni.Pk Z E k).coeff a =
        ∑ α, ((c α : ℝ) : ℂ) • ((List.ofFn (fun i : Fin a => Gm α i.castSucc * E)).prod *
          Gm α (Fin.last a)) := by
  obtain ⟨L, c, g, B, hB, hid, hbd⟩ := hsep
  set U := (hZ.eigenvectorUnitary : Mat d) with hU
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hZ.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Unitary.mul_star_self_of_mem hZ.eigenvectorUnitary.2
  refine ⟨L, c, fun α i => cfc (g α i) Z, ?_, fun E => ?_⟩
  · refine le_trans (Finset.sum_le_sum (fun α _ => ?_)) hbd
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine Finset.prod_le_prod (fun i _ => opNorm_nonneg' _) (fun i _ => ?_)
    exact OTDUni.opNorm_cfc_le hZ _ (hB α i).1 (fun b => (hB α i).2 _ (hspec b))
  · have hS := OTDUni.sum_coeff_path hZ p E a
    set S := ∑ k ∈ p.support, ((p.coeff k : ℝ) : ℂ) • (OTDUni.Pk Z E k).coeff a with hSdef
    have hS' : S = U * (star U * S * U) * star U := by
      simp only [← Matrix.mul_assoc]; rw [hUU', Matrix.one_mul, Matrix.mul_assoc, hUU', Matrix.mul_one]
    rw [hS', hS]
    rw [OTDUni.Path_congr _ _ I hspec _ (fun x => ∑ α, c α * ∏ i, g α i (x i)) hid, OTDUni.Path_sum]
    simp only [OTDUni.Path_smul, OTDUni.Path_prod, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [OTDUni.conj_prod U hUU E a (fun i => Matrix.diagonal (fun b => ((g α i (hZ.eigenvalues b) : ℝ) : ℂ)))]
    simp only [OTDUni.cfc_explicit hZ]
    rfl

/-! ### composition with a polynomial perturbation -/

def Bconv (m : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => if j = 0 then 1 else 0
  | a+1, j => ∑ q ∈ Finset.HasAntidiagonal.antidiagonal j, (if q.1 = 0 then 0 else m q.1) * Bconv m a q.2

lemma Bconv_nonneg {m : ℕ → ℝ} (hm : ∀ l, 0 ≤ m l) : ∀ a j, 0 ≤ Bconv m a j
  | 0, j => by simp only [Bconv]; split_ifs <;> norm_num
  | a+1, j => by
    simp only [Bconv]
    refine Finset.sum_nonneg (fun q _ => mul_nonneg ?_ (Bconv_nonneg hm a q.2))
    split_ifs; exact le_rfl; exact hm _

lemma mor_cast {i j : ℕ} {Ψ : Mat d → Mat d → Mat d} {M : ℝ} (h : MOR i Ψ M) (hij : i = j) :
    MOR j Ψ M := hij ▸ h

theorem comp_mor (Dt : Mat d → Mat d → Polynomial (Mat d)) (m : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l)
    (h0 : ∀ E₀ E₁, (Dt E₀ E₁).coeff 0 = 0)
    (hD : ∀ l, 1 ≤ l → MOR l (fun E₀ E₁ => (Dt E₀ E₁).coeff l) (m l)) :
    ∀ (a : ℕ) (Gm : Fin (a+1) → Mat d) (j : ℕ),
      MOR j (fun E₀ E₁ => ((List.ofFn (fun i : Fin a => Polynomial.C (Gm i.castSucc) * Dt E₀ E₁)).prod *
        Polynomial.C (Gm (Fin.last a))).coeff j) ((∏ i, opNorm (Gm i)) * Bconv m a j)
  | 0, Gm, j => by
    simp only [List.ofFn_zero, List.prod_nil, one_mul, Polynomial.coeff_C, Bconv, Fin.prod_univ_one]
    by_cases hj : j = 0
    · subst hj; simp only [if_true, mul_one]
      refine mor_mono (mor_const (Gm (Fin.last 0))) (le_of_eq ?_)
      rw [Fin.prod_univ_one]; rfl
    · simp only [if_neg hj, mul_zero]; exact mor_zero j
  | a+1, Gm, j => by
    have ih := comp_mor Dt m hm h0 hD a (fun i => Gm i.succ)
    have hsplit : ∀ E₀ E₁, ((List.ofFn (fun i : Fin (a+1) => Polynomial.C (Gm i.castSucc) * Dt E₀ E₁)).prod *
        Polynomial.C (Gm (Fin.last (a+1)))).coeff j =
        ∑ q ∈ Finset.HasAntidiagonal.antidiagonal j, Gm 0 * (Dt E₀ E₁).coeff q.1 *
          ((List.ofFn (fun i : Fin a => Polynomial.C (Gm i.succ.castSucc) * Dt E₀ E₁)).prod *
            Polynomial.C (Gm (Fin.last a).succ)).coeff q.2 := by
      intro E₀ E₁
      rw [List.ofFn_succ, List.prod_cons, _root_.mul_assoc (Polynomial.C _ * _), Polynomial.coeff_mul]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp only [Fin.castSucc_zero, Polynomial.coeff_C_mul, Fin.succ_castSucc]
      rfl
    have hterm : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal j, MOR j (fun E₀ E₁ => Gm 0 * (Dt E₀ E₁).coeff q.1 *
          ((List.ofFn (fun i : Fin a => Polynomial.C (Gm i.succ.castSucc) * Dt E₀ E₁)).prod *
            Polynomial.C (Gm (Fin.last a).succ)).coeff q.2)
        (opNorm (Gm 0) * (if q.1 = 0 then 0 else m q.1) * ((∏ i : Fin (a+1), opNorm (Gm i.succ)) * Bconv m a q.2)) := by
      intro q hq
      have hsum : q.1 + q.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
      by_cases hq0 : q.1 = 0
      · simp only [hq0, if_true, mul_zero, zero_mul, h0]
        refine mor_congr (fun E₀ E₁ => ?_) (mor_zero j)
        simp
      · simp only [if_neg hq0]
        have h1 := mor_mul (mor_mul (mor_const (Gm 0)) (hD q.1 (by omega))) (ih q.2)
        refine mor_cast (mor_congr (fun E₀ E₁ => rfl) h1) (by omega)
    have := mor_sum (Finset.HasAntidiagonal.antidiagonal j) hterm
    refine mor_congr (fun E₀ E₁ => (hsplit E₀ E₁).symm) (mor_mono this (le_of_eq ?_))
    simp only [Bconv, Finset.mul_sum, Fin.prod_univ_succ]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have : (Fin.last a).succ = Fin.last (a+1) := rfl
    ring

/-! ### algebra of ordered bounds -/

lemma hob_congr {j : ℕ} {Φ Ψ : Mat d → Mat d → ℂ} {M : ℝ} (h : ∀ E₀ E₁, Φ E₀ E₁ = Ψ E₀ E₁)
    (hΦ : HasOrderedBound j Φ M) : HasOrderedBound j Ψ M := by
  obtain ⟨L, c, A, t, hid, hb⟩ := hΦ
  exact ⟨L, c, A, t, fun E₀ E₁ => (h E₀ E₁).symm.trans (hid E₀ E₁), hb⟩

lemma hob_mono {j : ℕ} {Φ : Mat d → Mat d → ℂ} {M M' : ℝ} (hΦ : HasOrderedBound j Φ M)
    (h : M ≤ M') : HasOrderedBound j Φ M' := by
  obtain ⟨L, c, A, t, hid, hb⟩ := hΦ
  exact ⟨L, c, A, t, hid, hb.trans h⟩

lemma hob_zero (j : ℕ) : HasOrderedBound j (fun _ _ : Mat d => (0:ℂ)) 0 :=
  ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun _ _ => by simp, by simp⟩

lemma hob_add {j : ℕ} {Φ₁ Φ₂ : Mat d → Mat d → ℂ} {M₁ M₂ : ℝ}
    (h₁ : HasOrderedBound j Φ₁ M₁) (h₂ : HasOrderedBound j Φ₂ M₂) :
    HasOrderedBound j (fun E₀ E₁ => Φ₁ E₀ E₁ + Φ₂ E₀ E₁) (M₁ + M₂) := by
  obtain ⟨L₁, c₁, A₁, t₁, hid₁, hb₁⟩ := h₁
  obtain ⟨L₂, c₂, A₂, t₂, hid₂, hb₂⟩ := h₂
  refine ⟨L₁ + L₂, Fin.append c₁ c₂, Fin.append A₁ A₂, Fin.append t₁ t₂, fun E₀ E₁ => ?_, ?_⟩
  · dsimp only
    rw [hid₁, hid₂, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact add_le_add hb₁ hb₂

lemma hob_smul {j : ℕ} {Φ : Mat d → Mat d → ℂ} {M : ℝ} (a : ℂ) (h : HasOrderedBound j Φ M) :
    HasOrderedBound j (fun E₀ E₁ => a * Φ E₀ E₁) (‖a‖ * M) := by
  obtain ⟨L, c, A, t, hid, hb⟩ := h
  refine ⟨L, fun α => a * c α, A, t, fun E₀ E₁ => ?_, ?_⟩
  · dsimp only
    rw [hid, Finset.mul_sum]; simp only [mul_assoc]
  · simp only [norm_mul, mul_assoc]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

lemma hob_sum {j : ℕ} {ι : Type*} (S : Finset ι) {Φ : ι → Mat d → Mat d → ℂ} {M : ι → ℝ}
    (h : ∀ i ∈ S, HasOrderedBound j (Φ i) (M i)) :
    HasOrderedBound j (fun E₀ E₁ => ∑ i ∈ S, Φ i E₀ E₁) (∑ i ∈ S, M i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hob_zero (d := d) j
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self a S)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := hob_add h1 h2
    refine hob_congr (fun E₀ E₁ => ?_) (hob_mono this (le_of_eq ?_))
    · rw [Finset.sum_insert ha]
    · rw [Finset.sum_insert ha]


theorem taylor_comp (p : Polynomial ℝ) (Zt : Mat d → Mat d → Polynomial (Mat d)) {Z : Mat d}
    (hZ : Z.IsHermitian) (hZ0 : ∀ E₀ E₁, (Zt E₀ E₁).coeff 0 = Z) {I : Set ℝ}
    (hspec : ∀ i, hZ.eigenvalues i ∈ I) (SB : ℕ → ℝ)
    (hsep : ∀ a, 1 ≤ a → a ≤ p.natDegree → HasSeparatedBound a I (dividedDifference p a) (SB a))
    (m : ℕ → ℝ) (hm : ∀ l, 0 ≤ m l)
    (hU : ∀ l, 1 ≤ l → MOR l (fun E₀ E₁ => (Zt E₀ E₁).coeff l) (m l)) {j : ℕ} (hj : 1 ≤ j) :
    HasOrderedBound j (fun E₀ E₁ => ((peval p (Zt E₀ E₁)).coeff j).trace)
      (∑ a ∈ Finset.Icc 1 p.natDegree, SB a * Bconv m a j) := by
  classical
  set N := p.natDegree with hN
  have hrep : ∀ a : ℕ, ∃ (L : ℕ) (c : Fin L → ℝ) (Gm : Fin L → Fin (a+1) → Mat d),
      (1 ≤ a → a ≤ N → (∑ α, |c α| * ∏ i, opNorm (Gm α i)) ≤ SB a) ∧
      (1 ≤ a → a ≤ N → ∀ E : Mat d, ∑ k ∈ p.support, ((p.coeff k : ℝ) : ℂ) • (OTDUni.Pk Z E k).coeff a =
        ∑ α, ((c α : ℝ) : ℂ) • ((List.ofFn (fun i : Fin a => Gm α i.castSucc * E)).prod *
          Gm α (Fin.last a))) := by
    intro a
    by_cases ha : 1 ≤ a ∧ a ≤ N
    · obtain ⟨L, c, Gm, hb, hid⟩ := coeff_rep p hZ hspec (hsep a ha.1 ha.2)
      exact ⟨L, c, Gm, fun _ _ => hb, fun _ _ => hid⟩
    · exact ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun h1 h2 => absurd ⟨h1, h2⟩ ha,
        fun h1 h2 => absurd ⟨h1, h2⟩ ha⟩
  choose L c Gm hb hid using hrep
  set Dt : Mat d → Mat d → Polynomial (Mat d) := fun E₀ E₁ => Zt E₀ E₁ - Polynomial.C Z with hDt
  have hD0 : ∀ E₀ E₁, (Dt E₀ E₁).coeff 0 = 0 := by
    intro E₀ E₁; simp [hDt, hZ0]
  have hDl : ∀ l, 1 ≤ l → MOR l (fun E₀ E₁ => (Dt E₀ E₁).coeff l) (m l) := by
    intro l hl
    refine mor_congr (fun E₀ E₁ => ?_) (hU l hl)
    simp [hDt, Polynomial.coeff_C, show l ≠ 0 by omega]
  set W : (a : ℕ) → Fin (L a) → Mat d → Mat d → Polynomial (Mat d) := fun a α E₀ E₁ =>
    (List.ofFn (fun i : Fin a => Polynomial.C (Gm a α i.castSucc) * Dt E₀ E₁)).prod *
      Polynomial.C (Gm a α (Fin.last a)) with hW
  -- the polynomial identity
  have hid2 : ∀ E₀ E₁, trP (peval p (Zt E₀ E₁)) = Polynomial.C (matrixEval p Z).trace +
      ∑ a ∈ Finset.Icc 1 N, ∑ α, Polynomial.C (((c a α : ℝ) : ℂ)) * trP (W a α E₀ E₁) := by
    intro E₀ E₁
    refine Polynomial.funext (fun z => ?_)
    set E := (Dt E₀ E₁).eval (z • (1 : Mat d)) with hE
    have hZt : (Zt E₀ E₁).eval (z • (1 : Mat d)) = Z + E := by
      rw [hE, hDt]; simp
    rw [trP_eval, peval_eval, hZt, matrixEval_expand, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_finset_sum]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), Matrix.trace_add]
    congr 1
    · congr 1
      unfold matrixEval
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Pk_coeff_zero]
    · rw [show Finset.Ico (0+1) (N+1) = Finset.Icc 1 N by ext; simp, Matrix.trace_sum]
      refine Finset.sum_congr rfl (fun a ha => ?_)
      have ha' := Finset.mem_Icc.1 ha
      rw [hid a ha'.1 ha'.2 E, Matrix.trace_sum, Polynomial.eval_finset_sum]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [Polynomial.eval_mul, Polynomial.eval_C, trP_eval, Matrix.trace_smul, smul_eq_mul]
      congr 2
      simp only [hW]
      rw [eval_central_mul, eval_central_list, List.map_ofFn, Polynomial.eval_C]
      congr 2
      refine List.ofFn_inj.2 (funext (fun i => ?_))
      simp only [Function.comp_apply, eval_central_mul, Polynomial.eval_C, hE]
  have hcoef : ∀ E₀ E₁, ((peval p (Zt E₀ E₁)).coeff j).trace =
      (∑ a ∈ Finset.Icc 1 N, ∑ α, ((c a α : ℝ) : ℂ) • (W a α E₀ E₁).coeff j).trace := by
    intro E₀ E₁
    rw [← trP_coeff, hid2, Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add,
      Polynomial.finset_sum_coeff, Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Polynomial.finset_sum_coeff, Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Polynomial.coeff_C_mul, trP_coeff, Matrix.trace_smul, smul_eq_mul]
  have hmor : MOR j (fun E₀ E₁ => ∑ a ∈ Finset.Icc 1 N, ∑ α, ((c a α : ℝ) : ℂ) • (W a α E₀ E₁).coeff j)
      (∑ a ∈ Finset.Icc 1 N, ∑ α, ‖((c a α : ℝ) : ℂ)‖ * ((∏ i, opNorm (Gm a α i)) * Bconv m a j)) :=
    mor_sum _ (fun a _ => mor_sum _ (fun α _ =>
      mor_smul _ (comp_mor Dt m hm hD0 hDl a (Gm a α) j)))
  have hhob := mor_trace hmor
  refine hob_mono (hob_congr (fun E₀ E₁ => (hcoef E₀ E₁).symm) hhob) ?_
  refine Finset.sum_le_sum (fun a ha => ?_)
  have ha' := Finset.mem_Icc.1 ha
  have hB0 := Bconv_nonneg hm a j
  calc ∑ α, ‖((c a α : ℝ) : ℂ)‖ * ((∏ i, opNorm (Gm a α i)) * Bconv m a j)
      = (∑ α, |c a α| * ∏ i, opNorm (Gm a α i)) * Bconv m a j := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [Complex.norm_real, Real.norm_eq_abs]; ring
    _ ≤ SB a * Bconv m a j := mul_le_mul_of_nonneg_right (hb a ha'.1 ha'.2) hB0

/-! ### divided differences under affine substitution; separated bounds for `q_{K,s}` -/

open Polynomial in
lemma DD_affine_X (c t : ℝ) : ∀ (n a : ℕ) (x : Fin (a+1) → ℝ),
    dividedDifference ((X ^ n : Polynomial ℝ).comp (C c + C t * X)) a x =
      t ^ a * dividedDifference (X ^ n) a (fun i => c + t * x i)
  | 0, a, x => by
    simp only [pow_zero, one_comp]
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp [OTDUni.DD_zero_order]
    · rw [show (1 : Polynomial ℝ) = C 1 by simp, OTDUni.DD_const 1 a h, OTDUni.DD_const 1 a h, mul_zero]
  | n+1, 0, x => by
    rw [OTDUni.DD_zero_order, OTDUni.DD_zero_order, eval_comp]; simp
  | n+1, b+1, x => by
    have e : (X ^ (n+1) : Polynomial ℝ).comp (C c + C t * X) =
        (C c + C t * X) * (X ^ n : Polynomial ℝ).comp (C c + C t * X) := by
      rw [pow_succ', mul_comp, X_comp]
    rw [e, add_mul, OTDUni.DD_add, mul_assoc, OTDUni.DD_smul, OTDUni.DD_smul, OTDUni.DD_X_mul,
      DD_affine_X c t n (b+1) x, DD_affine_X c t n b (Fin.tail x),
      show (X ^ (n+1) : Polynomial ℝ) = X * X ^ n by ring, OTDUni.DD_X_mul]
    have ht : (Fin.tail fun i => c + t * x i) = fun i => c + t * Fin.tail x i := rfl
    rw [ht]
    ring

open Polynomial in
lemma DD_affine (c t : ℝ) (p : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) :
    dividedDifference (p.comp (C c + C t * X)) a x =
      t ^ a * dividedDifference p a (fun i => c + t * x i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, OTDUni.DD_add, OTDUni.DD_add, hp, hq]; ring
  | monomial n r =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, OTDUni.DD_smul, OTDUni.DD_smul, DD_affine_X]
    ring

open Polynomial in
lemma DD_qScaled (K : ℕ) {s : ℝ} (a : ℕ) (x : Fin (a+1) → ℝ) :
    dividedDifference (qScaled K s) a x = s * (s⁻¹) ^ a * dividedDifference (q K) a (fun i => s⁻¹ * x i) := by
  unfold qScaled
  rw [OTDUni.DD_smul, show (C s⁻¹ * X : Polynomial ℝ) = C 0 + C s⁻¹ * X by simp, DD_affine]
  simp only [zero_add]; ring

lemma sep_q1 (K : ℕ) (hK : 2 ≤ K) :
    HasSeparatedBound 1 (Set.Icc (-(1/2)) (1/2)) (dividedDifference (q K) 1) (16 * K) := by
  have hsum := OTDUni.sep_sum K (fun l _ => OTDUni.sep_smul (OTDUni.cJ K l) (OTDUni.sepQ 1 l le_rfl))
  have hcongr := OTDUni.sep_congr hsum (fun x _ => OTDUni.DD_q K 1 le_rfl x)
  refine OTDUni.sep_mono hcongr ?_
  have hterm : ∀ l ∈ Finset.range K, |OTDUni.cJ K l| * OTDUni.bQ 1 l ≤ 16 := by
    intro l hl
    by_cases h0 : l = 0
    · subst h0; simp only [OTDUni.cJ, if_true, abs_zero, zero_mul]; norm_num
    · have hl1 : (1:ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
      have hc : |OTDUni.cJ K l| ≤ 4 / l := by
        unfold OTDUni.cJ; rw [if_neg h0]; exact OTDJackson.coef_bound K hK l h0
      have hc' : |OTDUni.cJ K l| ≤ 4 := hc.trans (by rw [div_le_iff₀ (by linarith)]; linarith)
      have hb := OTDUni.bQ_le 1 l le_rfl (by omega)
      simp only [Nat.sub_self, pow_zero, mul_one, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hb
      have hb0 : 0 ≤ OTDUni.bQ 1 l := by
        unfold OTDUni.bQ; rw [if_neg h0]; split_ifs
        · positivity
        · have : (0:ℝ) < (l:ℝ) - 1 := by
            have : (2:ℝ) ≤ l := by exact_mod_cast (by omega : 2 ≤ l)
            linarith
          positivity
      nlinarith [abs_nonneg (OTDUni.cJ K l)]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; linarith

lemma sep_affine {a : ℕ} {I J : Set ℝ} {f : (Fin (a+1) → ℝ) → ℝ} {M : ℝ} (c s : ℝ)
    (h : HasSeparatedBound a J f M) (hIJ : ∀ t ∈ I, c + s * t ∈ J) :
    HasSeparatedBound a I (fun x => f (fun i => c + s * x i)) M := by
  obtain ⟨L, cc, g, B, hB, hrep, hs⟩ := h
  refine ⟨L, cc, fun α i t => g α i (c + s * t), B, fun α i => ⟨(hB α i).1,
    fun t ht => (hB α i).2 _ (hIJ t ht)⟩, fun x hx => hrep _ (fun i => hIJ _ (hx i)), hs⟩

/-- separated bounds of `q_{K,s}` on `[-s/2, s/2]` -/
def SBq (K : ℕ) (s : ℝ) (a : ℕ) : ℝ :=
  if a = 1 then 16 * K else s * (s⁻¹)^a * (16^a * (K:ℝ)^(a-1) / (a.factorial : ℝ))

lemma sep_qS (K : ℕ) (hK : 2 ≤ K) {s : ℝ} (hs : 0 < s) (a : ℕ) (ha : 1 ≤ a) :
    HasSeparatedBound a (Set.Icc (-(s/2)) (s/2)) (dividedDifference (qScaled K s) a) (SBq K s a) := by
  have hmap : ∀ t ∈ Set.Icc (-(s/2)) (s/2), (0:ℝ) + s⁻¹ * t ∈ Set.Icc (-(1/2:ℝ)) (1/2) := by
    intro t ht
    have h1 := ht.1; have h2 := ht.2
    constructor
    · rw [zero_add, ← div_eq_inv_mul, le_div_iff₀ hs]; linarith
    · rw [zero_add, ← div_eq_inv_mul, div_le_iff₀ hs]; linarith
  have hfun : ∀ (f : (Fin (a+1) → ℝ) → ℝ) (M : ℝ), HasSeparatedBound a (Set.Icc (-(1/2)) (1/2)) f M →
      HasSeparatedBound a (Set.Icc (-(s/2)) (s/2)) (fun x => s * (s⁻¹)^a * f (fun i => 0 + s⁻¹ * x i))
        (|s * (s⁻¹)^a| * M) := by
    intro f M h
    exact OTDUni.sep_smul _ (sep_affine 0 s⁻¹ h hmap)
  have hcong : ∀ x, dividedDifference (qScaled K s) a x =
      s * (s⁻¹)^a * dividedDifference (q K) a (fun i => 0 + s⁻¹ * x i) := by
    intro x; rw [DD_qScaled]; simp
  have habs : |s * (s⁻¹)^a| = s * (s⁻¹)^a := abs_of_pos (by positivity)
  unfold SBq
  by_cases h1 : a = 1
  · subst h1
    rw [if_pos rfl]
    have := hfun _ _ (sep_q1 K hK)
    rw [habs] at this
    refine OTDUni.sep_mono (OTDUni.sep_congr this (fun x _ => hcong x)) (le_of_eq ?_)
    field_simp
  · rw [if_neg h1]
    have := hfun _ _ (OTDUni.sep_q K a hK (by omega))
    rw [habs] at this
    exact OTDUni.sep_congr this (fun x _ => hcong x)

/-! ### Chebyshev structure of the filter -/

open Polynomial

def Tc (n : ℕ) : Polynomial ℝ := (Chebyshev.T ℝ (n:ℤ)).comp (1 - X)
def Fp (m : ℕ) : Polynomial ℝ := ∑ k ∈ Finset.range m, C (OTDJackson.fa m k) * Chebyshev.T ℝ (k:ℤ)

lemma one_sub_X_eq : (1 - X : Polynomial ℝ) = C 1 + C (-1) * X := by simp; ring

lemma fej_poly (m : ℕ) (hm : 1 ≤ m) : (1 - X) * Fp m = 1 - Chebyshev.T ℝ (m:ℤ) := by
  refine Polynomial.eq_of_infinite_eval_eq _ _
    ((Set.Icc_infinite (by norm_num : (-1:ℝ) < 1)).mono (fun y hy => ?_))
  rw [Set.mem_setOf_eq]
  set θ := Real.arccos y
  have hy' : Real.cos θ = y := Real.cos_arccos hy.1 hy.2
  rw [← hy']
  simp only [eval_mul, eval_sub, eval_one, eval_X, Fp, eval_finset_sum, eval_C, Chebyshev.T_real_cos]
  have hf := OTDJackson.fej_id m θ
  unfold OTDJackson.Fej at hf
  rw [Finset.sum_range_succ] at hf
  have hfm : OTDJackson.fa m m = 0 := by
    unfold OTDJackson.fa; rw [if_neg (by omega)]; ring
  rw [hfm, zero_mul, add_zero] at hf
  push_cast at hf ⊢
  linarith

lemma Fp_natDegree (m : ℕ) : (Fp m).natDegree ≤ m - 1 := by
  unfold Fp
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun k hk => ?_)
  have hk' := Finset.mem_range.1 hk
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [Chebyshev.natDegree_T]; simp; omega

lemma rFilter_eq (m : ℕ) (hm : 1 ≤ m) : rFilter m = C (1 / (m:ℝ)^2) * (Fp m).comp (1 - X) := by
  set Q := (Fp m).comp (1 - X) with hQ
  have hp : (1 - (Chebyshev.T ℝ (m:ℤ)).comp (1 - X) : Polynomial ℝ) = X * Q := by
    have e := congrArg (fun P : Polynomial ℝ => P.comp (1 - X)) (fej_poly m hm)
    simp only [mul_comp, sub_comp, one_comp, X_comp] at e
    rw [hQ, ← e]; ring
  have hQdeg : Q.natDegree < m := by
    have h1 : Q.natDegree ≤ (Fp m).natDegree * (1 - X : Polynomial ℝ).natDegree := natDegree_comp_le
    have h2 : (1 - X : Polynomial ℝ).natDegree ≤ 1 := by
      rw [one_sub_X_eq]
      refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      exact (natDegree_C_mul_le _ _).trans (by simp)
    have h3 := Fp_natDegree m
    have : (Fp m).natDegree * (1 - X : Polynomial ℝ).natDegree ≤ m - 1 := by
      calc (Fp m).natDegree * (1 - X : Polynomial ℝ).natDegree ≤ (m - 1) * 1 := Nat.mul_le_mul h3 h2
        _ = m - 1 := by ring
    omega
  unfold rFilter
  simp only
  rw [hp]
  conv_rhs => rw [Q.as_sum_range' m hQdeg]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [coeff_X_mul, ← C_mul_X_pow_eq_monomial, ← mul_assoc, ← C_mul]; congr 2; ring

lemma fa_nonneg (m k : ℕ) (hk : k < m) : 0 ≤ OTDJackson.fa m k := by
  unfold OTDJackson.fa; split_ifs
  · positivity
  · have : (k:ℝ) < m := by exact_mod_cast hk
    linarith

lemma fa_sum (m : ℕ) : ∑ k ∈ Finset.range m, OTDJackson.fa m k = (m:ℝ)^2 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [OTDJackson.fa, Nat.succ_ne_zero, if_false, if_true]
  have : ∑ i ∈ Finset.range n, 2 * (((n+1 : ℕ) : ℝ) - ((i+1 : ℕ) : ℝ)) = (n:ℝ) * (n+1) := by
    have h2 := Finset.sum_range_id_mul_two n
    have e : ∀ i ∈ Finset.range n, 2 * (((n+1 : ℕ) : ℝ) - ((i+1 : ℕ) : ℝ)) = 2 * (n:ℝ) - 2 * (i:ℝ) := by
      intro i _; push_cast; ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum]
    have h3 : (∑ i ∈ Finset.range n, (i:ℝ)) * 2 = (n:ℝ) * (n - 1) := by
      have := congrArg (fun z : ℕ => (z : ℝ)) h2
      push_cast at this
      rw [this]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · rw [Nat.cast_sub (by omega)]; push_cast; ring
    linarith
  rw [this]; push_cast; ring

lemma Tc_mul (k k' : ℕ) : Tc k * Tc k' = C (1/2) * Tc (k + k') + C (1/2) * Tc (Int.natAbs ((k:ℤ) - k')) := by
  unfold Tc
  have h := Chebyshev.T_mul_T (R := ℝ) (k:ℤ) (k':ℤ)
  have habs : Chebyshev.T ℝ ((k:ℤ) - k') = Chebyshev.T ℝ ((Int.natAbs ((k:ℤ) - k') : ℕ) : ℤ) := by
    rcases Int.natAbs_eq ((k:ℤ) - k') with h1 | h1
    · conv_lhs => rw [h1]
    · conv_lhs => rw [h1]; rw [Chebyshev.T_neg]
  rw [habs] at h
  have hT : Chebyshev.T ℝ (k:ℤ) * Chebyshev.T ℝ (k':ℤ) =
      C (1/2) * Chebyshev.T ℝ ((k + k' : ℕ) : ℤ) + C (1/2) * Chebyshev.T ℝ ((Int.natAbs ((k:ℤ) - k') : ℕ) : ℤ) := by
    have h2 : (2 : Polynomial ℝ) = C 2 := rfl
    have e : Chebyshev.T ℝ (k:ℤ) * Chebyshev.T ℝ (k':ℤ) =
        C (1/2) * (2 * Chebyshev.T ℝ (k:ℤ) * Chebyshev.T ℝ (k':ℤ)) := by
      rw [h2, ← mul_assoc, ← mul_assoc, ← C_mul]; norm_num
    rw [e, h]; push_cast; ring
  rw [← mul_comp, hT, add_comp, mul_comp, mul_comp, C_comp]

/-! ### separated bounds for the filter -/

/-- a functional on polynomials that is linear -/
structure LinF (a : ℕ) where
  F : Polynomial ℝ → (Fin (a+1) → ℝ) → ℝ
  add : ∀ p q x, F (p + q) x = F p x + F q x
  smul : ∀ c p x, F (C c * p) x = c * F p x

lemma LinF.zero {a : ℕ} (Φ : LinF a) (x : Fin (a+1) → ℝ) : Φ.F 0 x = 0 := by
  have := Φ.smul 0 0 x; simpa using this

lemma LinF.sum {a : ℕ} (Φ : LinF a) (n : ℕ) (P : ℕ → Polynomial ℝ) (x : Fin (a+1) → ℝ) :
    Φ.F (∑ k ∈ Finset.range n, P k) x = ∑ k ∈ Finset.range n, Φ.F (P k) x := by
  induction n with
  | zero => simp [Φ.zero]
  | succ n ih => rw [Finset.sum_range_succ, Φ.add, ih, Finset.sum_range_succ]

def ddF (a : ℕ) : LinF a where
  F := fun p x => dividedDifference p a x
  add := fun p q x => OTDUni.DD_add p q a x
  smul := fun c p x => OTDUni.DD_smul c p a x

def ddwF (a : ℕ) (r : Fin (a+1)) : LinF a where
  F := fun p x => Real.sqrt (x r) * dividedDifference p a x
  add := fun p q x => by rw [OTDUni.DD_add]; ring
  smul := fun c p x => by rw [OTDUni.DD_smul]; ring

def gam (m k : ℕ) : ℝ := OTDJackson.fa m k / (m:ℝ)^2

lemma m_facts {b : ℝ} (hb0 : 0 < b) (hb : b < 1/32) :
    2 ≤ ⌊1 / Real.sqrt (8*b)⌋₊ ∧ ((⌊1 / Real.sqrt (8*b)⌋₊ : ℕ) : ℝ)^2 ≤ 1 / (8*b) := by
  have h8 : 0 < 8 * b := by positivity
  have hs : 0 < Real.sqrt (8*b) := Real.sqrt_pos.2 h8
  have hs2 : Real.sqrt (8*b) < 1/2 := by
    rw [Real.sqrt_lt' (by norm_num)]; linarith
  have hge : (2:ℝ) ≤ 1 / Real.sqrt (8*b) := by
    rw [le_div_iff₀ hs]; linarith
  refine ⟨?_, ?_⟩
  · have := Nat.le_floor (n := 2) (by exact_mod_cast hge)
    exact this
  · have hf := Nat.floor_le (le_trans (by norm_num) hge)
    have h0 : (0:ℝ) ≤ ⌊1 / Real.sqrt (8*b)⌋₊ := Nat.cast_nonneg _
    calc ((⌊1 / Real.sqrt (8*b)⌋₊ : ℕ) : ℝ)^2 ≤ (1 / Real.sqrt (8*b))^2 := pow_le_pow_left₀ h0 hf 2
      _ = 1 / (8*b) := by rw [div_pow, Real.sq_sqrt h8.le, one_pow]

lemma filter_expand {b : ℝ} (hb0 : 0 < b) (hb : b < 1/32) :
    let m := ⌊1 / Real.sqrt (8*b)⌋₊
    filter b = ∑ k ∈ Finset.range m, C (2 * gam m k) * Tc k +
      ∑ k ∈ Finset.range m, ∑ k' ∈ Finset.range m,
        C (-(gam m k * gam m k' / 2)) * (Tc (k + k') + Tc (Int.natAbs ((k:ℤ) - k'))) := by
  intro m
  have hm : 1 ≤ m := by have := (m_facts hb0 hb).1; omega
  have hr : rFilter m = ∑ k ∈ Finset.range m, C (gam m k) * Tc k := by
    rw [rFilter_eq m hm, Fp, sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_comp, C_comp, ← mul_assoc, ← C_mul, gam, Tc]; congr 2; ring
  unfold filter
  rw [if_neg (by linarith)]
  simp only
  rw [hr, sq, Finset.sum_mul_sum]
  rw [Finset.mul_sum]
  have e1 : ∀ k ∈ Finset.range m, ∀ k' ∈ Finset.range m, C (gam m k) * Tc k * (C (gam m k') * Tc k') =
      C (gam m k * gam m k' / 2) * (Tc (k + k') + Tc (Int.natAbs ((k:ℤ) - k'))) := by
    intro k _ k' _
    have := Tc_mul k k'
    calc C (gam m k) * Tc k * (C (gam m k') * Tc k') = C (gam m k) * C (gam m k') * (Tc k * Tc k') := by ring
      _ = _ := by
        rw [this, ← C_mul, mul_add, ← mul_assoc, ← mul_assoc, ← C_mul, ← mul_add,
          show gam m k * gam m k' / 2 = gam m k * gam m k' * (1/2) by ring]
  rw [Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun k' hk' => e1 k hk k' hk'))]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (2 : Polynomial ℝ) = C 2 from rfl, ← mul_assoc, ← C_mul]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    rw [C_neg, neg_mul]

lemma gam_nonneg (m k : ℕ) (hk : k < m) : 0 ≤ gam m k := div_nonneg (fa_nonneg m k hk) (by positivity)

lemma gam_sum (m : ℕ) (hm : 1 ≤ m) : ∑ k ∈ Finset.range m, gam m k = 1 := by
  unfold gam; rw [← Finset.sum_div, fa_sum]; field_simp

theorem sep_filter_gen {a : ℕ} (Φ : LinF a) (I : Set ℝ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1/32)
    (S : ℕ → ℝ) (Smax : ℝ) (hS : ∀ n, HasSeparatedBound a I (Φ.F (Tc n)) (S n))
    (hSle : ∀ n, n ≤ 2 * ⌊1 / Real.sqrt (8*b)⌋₊ → S n ≤ Smax) (hS0 : ∀ n, 0 ≤ S n) :
    HasSeparatedBound a I (Φ.F (filter b)) (3 * Smax) := by
  set m := ⌊1 / Real.sqrt (8*b)⌋₊ with hmdef
  have hm : 1 ≤ m := by have := (m_facts hb0 hb).1; omega
  have hexp := filter_expand hb0 hb
  simp only at hexp
  rw [← hmdef] at hexp
  have hval : ∀ x, Φ.F (filter b) x = ∑ k ∈ Finset.range m, (2 * gam m k) * Φ.F (Tc k) x +
      ∑ k ∈ Finset.range m, ∑ k' ∈ Finset.range m,
        (-(gam m k * gam m k' / 2)) * (Φ.F (Tc (k + k')) x + Φ.F (Tc (Int.natAbs ((k:ℤ) - k'))) x) := by
    intro x
    rw [hexp, Φ.add, Φ.sum, Φ.sum]
    congr 1
    · refine Finset.sum_congr rfl (fun k _ => ?_); rw [Φ.smul]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Φ.sum]
      refine Finset.sum_congr rfl (fun k' _ => ?_); rw [Φ.smul, Φ.add]
  have h1 := OTDUni.sep_sum m (fun k _ => OTDUni.sep_smul (2 * gam m k) (hS k))
  have h2 := OTDUni.sep_sum m (fun k _ => OTDUni.sep_sum m (fun k' _ =>
    OTDUni.sep_smul (-(gam m k * gam m k' / 2)) (OTDUni.sep_add (hS (k + k')) (hS (Int.natAbs ((k:ℤ) - k'))))))
  have h3 := OTDUni.sep_add h1 h2
  refine OTDUni.sep_mono (OTDUni.sep_congr h3 (fun x _ => hval x)) ?_
  have hSmax0 : 0 ≤ Smax := (hS0 0).trans (hSle 0 (by omega))
  have hA : ∑ k ∈ Finset.range m, |2 * gam m k| * S k ≤ 2 * Smax := by
    calc ∑ k ∈ Finset.range m, |2 * gam m k| * S k ≤ ∑ k ∈ Finset.range m, (2 * gam m k) * Smax := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hk := Finset.mem_range.1 hk
          rw [abs_of_nonneg (by have := gam_nonneg m k hk; positivity)]
          exact mul_le_mul_of_nonneg_left (hSle k (by omega)) (by have := gam_nonneg m k hk; positivity)
      _ = 2 * Smax := by rw [← Finset.sum_mul, ← Finset.mul_sum, gam_sum m hm]; ring
  have hB : ∑ k ∈ Finset.range m, ∑ k' ∈ Finset.range m,
      |-(gam m k * gam m k' / 2)| * (S (k + k') + S (Int.natAbs ((k:ℤ) - k'))) ≤ Smax := by
    calc ∑ k ∈ Finset.range m, ∑ k' ∈ Finset.range m,
          |-(gam m k * gam m k' / 2)| * (S (k + k') + S (Int.natAbs ((k:ℤ) - k')))
        ≤ ∑ k ∈ Finset.range m, ∑ k' ∈ Finset.range m, (gam m k * gam m k') * Smax := by
          refine Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun k' hk' => ?_))
          have hk := Finset.mem_range.1 hk
          have hk' := Finset.mem_range.1 hk'
          have g1 := gam_nonneg m k hk
          have g2 := gam_nonneg m k' hk'
          rw [abs_neg, abs_of_nonneg (by positivity)]
          have s1 := hSle (k + k') (by omega)
          have s2 := hSle (Int.natAbs ((k:ℤ) - k')) (by omega)
          nlinarith [mul_nonneg g1 g2]
      _ = Smax := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum, gam_sum m hm]
          ring
  linarith

lemma Tc_natDegree (n : ℕ) : (Tc n).natDegree ≤ n := by
  unfold Tc
  refine natDegree_comp_le.trans ?_
  rw [Chebyshev.natDegree_T]
  have h2 : (1 - X : Polynomial ℝ).natDegree ≤ 1 := by
    rw [one_sub_X_eq]
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le _ _).trans (by simp)
  simp only [Int.natAbs_natCast]
  calc n * (1 - X : Polynomial ℝ).natDegree ≤ n * 1 := Nat.mul_le_mul_left _ h2
    _ = n := by ring

lemma sepTc_u (n a : ℕ) (ha : 1 ≤ a) :
    HasSeparatedBound a (Set.Icc 0 1) (dividedDifference (Tc n) a)
      ((2 * (n:ℝ)^2)^a / ((2*a).factorial : ℝ)) := by
  by_cases han : a ≤ n
  · have h1 := (lemma_B_1 n a ha han).1
    have hmap : ∀ t ∈ Set.Icc (0:ℝ) 1, (1:ℝ) + (-1) * t ∈ Set.Icc (-1:ℝ) 1 := by
      intro t ht; constructor <;> linarith [ht.1, ht.2]
    have h2 := OTDUni.sep_smul ((-1:ℝ)^a) (sep_affine 1 (-1) h1 hmap)
    rw [abs_pow, abs_neg, abs_one, one_pow, one_mul] at h2
    refine OTDUni.sep_congr h2 (fun x _ => ?_)
    rw [Tc, one_sub_X_eq, DD_affine]
  · refine OTDUni.sep_mono (OTDUni.sep_congr (OTDUni.sep_zero a _) (fun x _ => ?_)) (by positivity)
    exact OTDUni.DD_low (Tc n) a x (by have := Tc_natDegree n; omega)

lemma sepTc_w (n a : ℕ) (ha : 1 ≤ a) (r : Fin (a+1)) (hr : r.val = 0 ∨ r.val = a) :
    HasSeparatedBound a (Set.Icc 0 1) (fun x => Real.sqrt (x r) * dividedDifference (Tc n) a x)
      ((2:ℝ)^a * (n:ℝ)^(2*a-1) / ((2*a-1).factorial : ℝ)) := by
  by_cases han : a ≤ n
  · exact (lemma_B_1 n a ha han).2.2 r hr
  · refine OTDUni.sep_mono (OTDUni.sep_congr (OTDUni.sep_zero a _) (fun x _ => ?_)) (by positivity)
    rw [OTDUni.DD_low (Tc n) a x (by have := Tc_natDegree n; omega), mul_zero]

theorem sep_filter_u {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (a : ℕ) (ha : 1 ≤ a) :
    HasSeparatedBound a (Set.Icc 0 1) (dividedDifference (filter b) a)
      (2^(a+2) / b^a / ((2*a).factorial : ℝ)) := by
  by_cases hb : 1/32 ≤ b
  · have : filter b = 1 := by unfold filter; rw [if_pos hb]
    rw [this]
    refine OTDUni.sep_mono (OTDUni.sep_congr (OTDUni.sep_zero a _) (fun x _ => ?_)) (by positivity)
    rw [show (1 : Polynomial ℝ) = C 1 by simp, OTDUni.DD_const 1 a ha]
  · push_neg at hb
    obtain ⟨hm2, hmsq⟩ := m_facts hb0 hb
    set m := ⌊1 / Real.sqrt (8*b)⌋₊ with hmdef
    have h := sep_filter_gen (ddF a) (Set.Icc 0 1) hb0 hb
      (fun n => (2 * (n:ℝ)^2)^a / ((2*a).factorial : ℝ)) ((2 / b)^a / ((2*a).factorial : ℝ))
      (fun n => sepTc_u n a ha) (fun n hn => ?_) (fun n => by positivity)
    · refine OTDUni.sep_mono h ?_
      have e : 3 * ((2 / b)^a / ((2*a).factorial : ℝ)) = (3 * 2^a) / b^a / ((2*a).factorial : ℝ) := by
        rw [div_pow]; ring
      rw [e]
      have : (3:ℝ) * 2^a ≤ 2^(a+2) := by rw [pow_add]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) a]
      gcongr
    · have hn' : (n:ℝ) ≤ 2 * m := by exact_mod_cast hn
      have hn2 : 2 * (n:ℝ)^2 ≤ 2 / b := by
        have h0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
        have h1 : (n:ℝ)^2 ≤ 4 * (m:ℝ)^2 := by nlinarith
        have h2 : 4 * (m:ℝ)^2 ≤ 1 / (2 * b) := by
          calc 4 * (m:ℝ)^2 ≤ 4 * (1 / (8 * b)) := by gcongr
            _ = 1 / (2 * b) := by field_simp; ring
        have h3 : 2 * (1 / (2 * b)) ≤ 2 / b := by
          rw [show 2 * (1 / (2 * b)) = 1 / b by field_simp]
          exact div_le_div_of_nonneg_right (by norm_num) hb0.le
        linarith
      gcongr
theorem sep_filter_w {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (a : ℕ) (ha : 1 ≤ a) (r : Fin (a+1))
    (hr : r.val = 0 ∨ r.val = a) :
    HasSeparatedBound a (Set.Icc 0 1) (fun x => Real.sqrt (x r) * dividedDifference (filter b) a x)
      (2^(a+4) * Real.sqrt b / b^a / ((2*a-1).factorial : ℝ)) := by
  by_cases hb : 1/32 ≤ b
  · have : filter b = 1 := by unfold filter; rw [if_pos hb]
    rw [this]
    refine OTDUni.sep_mono (OTDUni.sep_congr (OTDUni.sep_zero a _) (fun x _ => ?_)) (by positivity)
    rw [show (1 : Polynomial ℝ) = C 1 by simp, OTDUni.DD_const 1 a ha, mul_zero]
  · push_neg at hb
    obtain ⟨hm2, hmsq⟩ := m_facts hb0 hb
    set m := ⌊1 / Real.sqrt (8*b)⌋₊ with hmdef
    have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
    have key : (1 / Real.sqrt b)^(2*a-1) = Real.sqrt b / b^a := by
      have e1 : b^a = (Real.sqrt b)^(2*a-1) * Real.sqrt b := by
        rw [← pow_succ, show 2*a-1+1 = 2*a by omega, pow_mul, Real.sq_sqrt hb0.le]
      rw [e1, one_div, inv_pow]; field_simp
    have h := sep_filter_gen (ddwF a r) (Set.Icc 0 1) hb0 hb
      (fun n => (2:ℝ)^a * (n:ℝ)^(2*a-1) / ((2*a-1).factorial : ℝ))
      ((2:ℝ)^a * (Real.sqrt b / b^a) / ((2*a-1).factorial : ℝ))
      (fun n => sepTc_w n a ha r hr) (fun n hn => ?_) (fun n => by positivity)
    · refine OTDUni.sep_mono h ?_
      have e : 3 * ((2:ℝ)^a * (Real.sqrt b / b^a) / ((2*a-1).factorial : ℝ)) =
          (3 * 2^a) * Real.sqrt b / b^a / ((2*a-1).factorial : ℝ) := by ring
      rw [e]
      have : (3:ℝ) * 2^a ≤ 2^(a+4) := by rw [pow_add]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) a]
      gcongr
    · have hn' : (n:ℝ) ≤ 2 * m := by exact_mod_cast hn
      have h0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
      have hn2 : (n:ℝ)^2 ≤ 1 / b := by
        have h1 : (n:ℝ)^2 ≤ 4 * (m:ℝ)^2 := by nlinarith
        have h2 : 4 * (m:ℝ)^2 ≤ 1 / (2 * b) := by
          calc 4 * (m:ℝ)^2 ≤ 4 * (1 / (8 * b)) := by gcongr
            _ = 1 / (2 * b) := by field_simp; ring
        have h3 : 1 / (2 * b) ≤ 1 / b := by
          apply div_le_div_of_nonneg_left (by norm_num) hb0; linarith
        linarith
      have hn3 : (n:ℝ) ≤ 1 / Real.sqrt b := by
        rw [le_div_iff₀ hsb]
        have : ((n:ℝ) * Real.sqrt b)^2 ≤ 1 := by
          rw [mul_pow, Real.sq_sqrt hb0.le]
          calc (n:ℝ)^2 * b ≤ (1 / b) * b := by gcongr
            _ = 1 := by field_simp
        nlinarith [mul_nonneg h0 hsb.le]
      show (2:ℝ)^a * (n:ℝ)^(2*a-1) / ((2*a-1).factorial : ℝ) ≤
        (2:ℝ)^a * (Real.sqrt b / b^a) / ((2*a-1).factorial : ℝ)
      rw [← key]
      gcongr

/-! ### functional calculus helpers -/

section fc
variable {X : Mat d} (hX : X.IsHermitian)
include hX

lemma cfc_mul2 (f g : ℝ → ℝ) : cfc f X * cfc g X = cfc (fun t => f t * g t) X := by
  rw [OTDUni.cfc_explicit hX, OTDUni.cfc_explicit hX, OTDUni.cfc_explicit hX]
  set U := (hX.eigenvectorUnitary : Mat d)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (OTDUni.U_mem hX)
  calc U * diagonal (fun i => ((f (hX.eigenvalues i) : ℝ) : ℂ)) * star U *
        (U * diagonal (fun i => ((g (hX.eigenvalues i) : ℝ) : ℂ)) * star U)
      = U * diagonal (fun i => ((f (hX.eigenvalues i) : ℝ) : ℂ)) * (star U * U) *
          diagonal (fun i => ((g (hX.eigenvalues i) : ℝ) : ℂ)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]; push_cast; rfl

lemma cfc_congr2 {f g : ℝ → ℝ} (h : ∀ i, f (hX.eigenvalues i) = g (hX.eigenvalues i)) :
    cfc f X = cfc g X := by
  rw [OTDUni.cfc_explicit hX, OTDUni.cfc_explicit hX]; simp only [h]

lemma cfc_zero2 {f : ℝ → ℝ} (h : ∀ i, f (hX.eigenvalues i) = 0) : cfc f X = 0 := by
  rw [cfc_congr2 hX (g := fun _ => 0) h, OTDUni.cfc_explicit hX]; simp

lemma psd_cfc2 (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hX.eigenvalues i)) : (cfc f X).PosSemidef := by
  rw [OTDUni.cfc_explicit hX]
  have hD : (diagonal (fun i => ((f (hX.eigenvalues i) : ℝ) : ℂ))).PosSemidef :=
    PosSemidef.diagonal (fun i => by simpa using hf i)
  have := hD.mul_mul_conjTranspose_same (hX.eigenvectorUnitary : Mat d)
  rwa [← Matrix.star_eq_conjTranspose] at this

lemma opNorm_sandwich2 {Y : Mat d} (hY : Y.IsHermitian) (hlo : lePSD (-X) Y) (hhi : lePSD Y X)
    (g : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) (hg : ∀ i, hX.eigenvalues i * g (hX.eigenvalues i)^2 ≤ c) :
    opNorm (cfc g X * Y * cfc g X) ≤ c := by
  set G := cfc g X with hG
  have hGH : G.IsHermitian := OTDUni.cfc_herm hX g
  have hZH : (G * Y * G).IsHermitian := by
    show (G * Y * G)ᴴ = G * Y * G
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hGH.eq, hY.eq, Matrix.mul_assoc]
  refine OTDUni.opNorm_le_of_quad hZH hc (fun v => ?_)
  set u := G *ᵥ v with hu
  have hq : ∀ M : Mat d, star v ⬝ᵥ ((G * M * G) *ᵥ v) = star u ⬝ᵥ (M *ᵥ u) := by
    intro M
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hu,
      Matrix.star_mulVec, hGH.eq]
  rw [hq Y]
  have h1 := OTDUni.re_nonneg_of_psd hlo u
  have h2 := OTDUni.re_nonneg_of_psd hhi u
  rw [sub_neg_eq_add, Matrix.add_mulVec, dotProduct_add, Complex.add_re] at h1
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at h2
  have hX' : (star u ⬝ᵥ (X *ᵥ u)).re ≤ c * (star v ⬝ᵥ v).re := by
    rw [← hq X]
    have e : G * X * G = cfc (fun x => x * g x ^ 2) X := by
      have h1 : cfc g X * cfc (fun x : ℝ => x) X * cfc g X = cfc (fun x => x * g x ^ 2) X := by
        rw [cfc_mul2 hX, cfc_mul2 hX]; congr 1; funext x; ring
      rwa [cfc_id' ℝ X hX.isSelfAdjoint] at h1
    rw [e, OTDUni.quad_cfc hX]
    set y := star (hX.eigenvectorUnitary : Mat d) *ᵥ v
    have hyy : (star v ⬝ᵥ v) = star y ⬝ᵥ y := (OTDUni.unitary_norm _ (OTDUni.U_mem hX) v).symm
    rw [hyy, OTDUni.sum_normsq y]
    simp only [Complex.re_sum, Complex.ofReal_re]
    have h1 : ∀ i, ((((hX.eigenvalues i * g (hX.eigenvalues i) ^ 2 : ℝ)) : ℂ) * (star (y i) * y i)).re =
        (hX.eigenvalues i * g (hX.eigenvalues i) ^ 2) * ‖y i‖^2 := by
      intro i
      have : star (y i) * y i = ((‖y i‖^2 : ℝ) : ℂ) := by
        rw [mul_comm]; show y i * (starRingEnd ℂ) (y i) = _
        rw [Complex.mul_conj', Complex.ofReal_pow]
      rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp only [h1]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hg i) (sq_nonneg _))
  rw [abs_le]; constructor <;> linarith

end fc

/-- PSD matrices vanish on the kernel of their compression -/
lemma psd_kernel {A Q : Mat d} (hA : A.PosSemidef) (hQ : Q.IsHermitian) (h : Q * A * Q = 0) :
    A * Q = 0 := by
  have hAH := hA.1
  set R := cfc Real.sqrt A with hR
  have hRH : R.IsHermitian := OTDUni.cfc_herm hAH _
  have hRR : R * R = A := by
    rw [hR, cfc_mul2 hAH, cfc_congr2 hAH (g := fun x => x) (fun i => ?_), cfc_id' ℝ A hAH.isSelfAdjoint]
    exact Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
  have h1 : (R * Q)ᴴ * (R * Q) = 0 := by
    rw [Matrix.conjTranspose_mul, hRH.eq, hQ.eq, Matrix.mul_assoc, ← Matrix.mul_assoc R R, hRR,
      ← Matrix.mul_assoc]; exact h
  have h2 : R * Q = 0 := by
    rw [← Matrix.trace_conjTranspose_mul_self_eq_zero_iff, h1, Matrix.trace_zero]
  rw [← hRR, Matrix.mul_assoc, h2, Matrix.mul_zero]

lemma cfc_add2 {X : Mat d} (hX : X.IsHermitian) (f g : ℝ → ℝ) :
    cfc f X + cfc g X = cfc (fun t => f t + g t) X := by
  rw [OTDUni.cfc_explicit hX, OTDUni.cfc_explicit hX, OTDUni.cfc_explicit hX, ← Matrix.add_mul,
    ← Matrix.mul_add, diagonal_add]; push_cast; rfl

lemma cfc_one2 {X : Mat d} (hX : X.IsHermitian) : cfc (fun _ : ℝ => (1:ℝ)) X = 1 := by
  rw [OTDUni.cfc_explicit hX]; simp only [Complex.ofReal_one]
  rw [diagonal_one, Matrix.mul_one, Unitary.mul_star_self_of_mem (OTDUni.U_mem hX)]

theorem J_exists {X Y : Mat d} (hX0 : X.PosSemidef) (hY : Y.IsHermitian)
    (hlo : lePSD (-X) Y) (hhi : lePSD Y X) :
    ∃ J : Mat d, opNorm J ≤ 1 ∧ cfc Real.sqrt X * J * cfc Real.sqrt X = Y := by
  have hX := hX0.1
  have hx0 : ∀ i, 0 ≤ hX.eigenvalues i := fun i => hX0.eigenvalues_nonneg i
  set gP : ℝ → ℝ := fun x => if 0 < x then 1 / Real.sqrt x else 0 with hgP
  refine ⟨cfc gP X * Y * cfc gP X, ?_, ?_⟩
  · refine opNorm_sandwich2 hX hY hlo hhi gP zero_le_one (fun i => ?_)
    simp only [hgP]; split_ifs with h
    · rw [div_pow, Real.sq_sqrt (hx0 i), one_pow]; field_simp; exact le_rfl
    · simp
  · set Pi := cfc (fun x : ℝ => if 0 < x then (1:ℝ) else 0) X with hPi
    set Q := cfc (fun x : ℝ => if 0 < x then (0:ℝ) else 1) X with hQ
    have hQH : Q.IsHermitian := OTDUni.cfc_herm hX _
    have hPQ : Pi = 1 - Q := by
      rw [eq_sub_iff_add_eq, hPi, hQ, cfc_add2 hX, ← cfc_one2 hX]
      congr 1; funext x; split_ifs <;> ring
    have hsP : cfc Real.sqrt X * cfc gP X = Pi := by
      rw [cfc_mul2 hX, hPi]; refine cfc_congr2 hX (fun i => ?_)
      simp only [hgP]; split_ifs with h
      · field_simp [(Real.sqrt_pos.2 h).ne']
      · simp
    have hPs : cfc gP X * cfc Real.sqrt X = Pi := by
      rw [cfc_mul2 hX, hPi]; refine cfc_congr2 hX (fun i => ?_)
      simp only [hgP]; split_ifs with h
      · field_simp [(Real.sqrt_pos.2 h).ne']
      · simp
    have hXQ : X * Q = 0 := by
      have : X = cfc (fun x : ℝ => x) X := (cfc_id' ℝ X hX.isSelfAdjoint).symm
      rw [this, hQ, cfc_mul2 hX]
      refine cfc_zero2 hX (fun i => ?_)
      split_ifs with h
      · ring
      · have : hX.eigenvalues i = 0 := le_antisymm (not_lt.1 h) (hx0 i)
        rw [this]; ring
    have hQXQ : Q * X * Q = 0 := by rw [Matrix.mul_assoc, hXQ, Matrix.mul_zero]
    have hA : (Y + X).PosSemidef := by have := hlo; unfold lePSD at this; rwa [sub_neg_eq_add] at this
    have hB : (X - Y).PosSemidef := hhi
    have hQA := hA.conjTranspose_mul_mul_same Q
    have hQB := hB.conjTranspose_mul_mul_same Q
    rw [hQH.eq] at hQA hQB
    have hsum : Q * (Y + X) * Q + Q * (X - Y) * Q = 0 := by
      rw [← Matrix.add_mul, ← Matrix.mul_add]
      rw [show Y + X + (X - Y) = (2:ℂ) • X by rw [two_smul]; abel, Matrix.mul_smul, Matrix.smul_mul,
        hQXQ, smul_zero]
    have ht1 := (Complex.nonneg_iff.1 hQA.trace_nonneg).1
    have ht2 := (Complex.nonneg_iff.1 hQB.trace_nonneg).1
    have htr : (Q * (Y + X) * Q).trace.re + (Q * (X - Y) * Q).trace.re = 0 := by
      rw [← Complex.add_re, ← Matrix.trace_add, hsum, Matrix.trace_zero, Complex.zero_re]
    have hz : (Q * (Y + X) * Q).trace = 0 := by
      apply Complex.ext
      · simp only [Complex.zero_re]; linarith
      · have := (Complex.nonneg_iff.1 hQA.trace_nonneg).2; simp only [Complex.zero_im]; linarith
    have hQAQ : Q * (Y + X) * Q = 0 := (hQA.trace_eq_zero_iff).1 hz
    have hAQ := psd_kernel hA hQH hQAQ
    have hYQ : Y * Q = 0 := by
      have : Y * Q = (Y + X) * Q - X * Q := by rw [Matrix.add_mul]; abel
      rw [this, hAQ, hXQ, sub_zero]
    have hQY : Q * Y = 0 := by
      have := congrArg Matrix.conjTranspose hYQ
      rwa [Matrix.conjTranspose_mul, hQH.eq, hY.eq, Matrix.conjTranspose_zero] at this
    calc cfc Real.sqrt X * (cfc gP X * Y * cfc gP X) * cfc Real.sqrt X
        = (cfc Real.sqrt X * cfc gP X) * Y * (cfc gP X * cfc Real.sqrt X) := by
          simp only [Matrix.mul_assoc]
      _ = Pi * Y * Pi := by rw [hsP, hPs]
      _ = Y := by
          rw [hPQ, Matrix.sub_mul, Matrix.one_mul, hQY, sub_zero, Matrix.mul_sub, Matrix.mul_one, hYQ,
            sub_zero]

/-! ### coefficient matrices of the filtered variable -/

lemma Path_weight_right (j : ℕ) (lam : Fin d → ℝ) (E' : Mat d) (f : (Fin (j+1) → ℝ) → ℝ) (h : ℝ → ℝ) :
    OTDUni.Path j lam E' f * diagonal (fun b => ((h (lam b) : ℝ) : ℂ)) =
      OTDUni.Path j lam E' (fun x => f x * h (x (Fin.last j))) := by
  ext a b
  rw [Matrix.mul_diagonal]
  simp only [OTDUni.Path, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases hc : c 0 = a ∧ c (Fin.last j) = b
  · rw [if_pos hc, ← hc.2]; push_cast; ring
  · rw [if_neg hc]; ring

lemma Path_weight_left (j : ℕ) (lam : Fin d → ℝ) (E' : Mat d) (f : (Fin (j+1) → ℝ) → ℝ) (h : ℝ → ℝ) :
    diagonal (fun b => ((h (lam b) : ℝ) : ℂ)) * OTDUni.Path j lam E' f =
      OTDUni.Path j lam E' (fun x => h (x 0) * f x) := by
  ext a b
  rw [Matrix.diagonal_mul]
  simp only [OTDUni.Path, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases hc : c 0 = a ∧ c (Fin.last j) = b
  · rw [if_pos hc, ← hc.1]; push_cast; ring
  · rw [if_neg hc]; ring

theorem path_rep {Z : Mat d} (hZ : Z.IsHermitian) {I : Set ℝ} (hspec : ∀ i, hZ.eigenvalues i ∈ I)
    {a : ℕ} {F : (Fin (a+1) → ℝ) → ℝ} {M : ℝ} (hsep : HasSeparatedBound a I F M) :
    ∃ (L : ℕ) (c : Fin L → ℝ) (Gm : Fin L → Fin (a+1) → Mat d),
      (∑ α, |c α| * ∏ i, opNorm (Gm α i)) ≤ M ∧
      ∀ E : Mat d, (hZ.eigenvectorUnitary : Mat d) *
          OTDUni.Path a hZ.eigenvalues (star (hZ.eigenvectorUnitary : Mat d) * E *
            (hZ.eigenvectorUnitary : Mat d)) F * star (hZ.eigenvectorUnitary : Mat d) =
        ∑ α, ((c α : ℝ) : ℂ) • ((List.ofFn (fun i : Fin a => Gm α i.castSucc * E)).prod *
          Gm α (Fin.last a)) := by
  obtain ⟨L, c, g, B, hB, hid, hbd⟩ := hsep
  set U := (hZ.eigenvectorUnitary : Mat d) with hU
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hZ.eigenvectorUnitary.2
  refine ⟨L, c, fun α i => cfc (g α i) Z, ?_, fun E => ?_⟩
  · refine le_trans (Finset.sum_le_sum (fun α _ => ?_)) hbd
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine Finset.prod_le_prod (fun i _ => opNorm_nonneg' _) (fun i _ => ?_)
    exact OTDUni.opNorm_cfc_le hZ _ (hB α i).1 (fun b => (hB α i).2 _ (hspec b))
  · rw [OTDUni.Path_congr _ _ I hspec _ (fun x => ∑ α, c α * ∏ i, g α i (x i)) hid, OTDUni.Path_sum]
    simp only [OTDUni.Path_smul, OTDUni.Path_prod, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [OTDUni.conj_prod U hUU E a (fun i => Matrix.diagonal (fun b => ((g α i (hZ.eigenvalues b) : ℝ) : ℂ)))]
    simp only [OTDUni.cfc_explicit hZ]
    rfl

lemma mor_prod : ∀ (a : ℕ) (Gm : Fin (a+1) → Mat d),
    MOR a (fun E₀ _ => (List.ofFn (fun i : Fin a => Gm i.castSucc * E₀)).prod * Gm (Fin.last a))
      (∏ i, opNorm (Gm i))
  | 0, Gm => by
    refine mor_congr (fun E₀ E₁ => by simp) (mor_mono (mor_const (Gm (Fin.last 0))) (le_of_eq ?_))
    rw [Fin.prod_univ_one]; rfl
  | a+1, Gm => by
    have ih := mor_prod a (fun i => Gm i.succ)
    have h := mor_mul (mor_mul (mor_const (Gm 0)) mor_e0) ih
    refine mor_cast (mor_congr (fun E₀ E₁ => ?_) (mor_mono h (le_of_eq ?_))) (by omega)
    · rw [List.ofFn_succ, List.prod_cons]
      simp only [Fin.castSucc_zero, Fin.succ_castSucc, Matrix.mul_assoc]
      rfl
    · rw [Fin.prod_univ_succ (fun i : Fin (a+2) => opNorm (Gm i))]; ring

/-- generic: a path representation gives an ordered matrix representation -/
theorem mor_of_path {Z : Mat d} (hZ : Z.IsHermitian) {I : Set ℝ} (hspec : ∀ i, hZ.eigenvalues i ∈ I)
    {a : ℕ} {F : (Fin (a+1) → ℝ) → ℝ} {M : ℝ} (hsep : HasSeparatedBound a I F M)
    (Ψ : Mat d → Mat d → Mat d)
    (hΨ : ∀ E₀ E₁, Ψ E₀ E₁ = (hZ.eigenvectorUnitary : Mat d) *
          OTDUni.Path a hZ.eigenvalues (star (hZ.eigenvectorUnitary : Mat d) * E₀ *
            (hZ.eigenvectorUnitary : Mat d)) F * star (hZ.eigenvectorUnitary : Mat d)) :
    MOR a Ψ M := by
  obtain ⟨L, c, Gm, hb, hid⟩ := path_rep hZ hspec hsep
  have := mor_sum (Finset.univ : Finset (Fin L)) (fun α _ => mor_smul ((c α : ℝ) : ℂ) (mor_prod a (Gm α)))
  refine mor_congr (fun E₀ E₁ => ?_) (mor_mono this ?_)
  · rw [hΨ, hid]
  · refine le_trans (le_of_eq ?_) hb
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]

def Ra (b : ℝ) (X E₀ : Mat d) (a : ℕ) : Mat d := (Rt b X E₀).coeff a

def uB (b : ℝ) (a : ℕ) : ℝ := 2^(a+2) / b^a / ((2*a).factorial : ℝ)
def wB (b : ℝ) (a : ℕ) : ℝ := 2^(a+4) * Real.sqrt b / b^a / ((2*a-1).factorial : ℝ)

lemma Ra_eq (b : ℝ) (X E₀ : Mat d) (a : ℕ) :
    Ra b X E₀ a = ∑ k ∈ (filter b).support, (((filter b).coeff k : ℝ) : ℂ) • (OTDUni.Pk X E₀ k).coeff a := by
  unfold Ra Rt peval
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.coeff_smul, Pk_eq]

section Rsec
variable {X : Mat d} (hX0 : X.PosSemidef) (hx1 : ∀ i, hX0.1.eigenvalues i ≤ 1)
include hX0 hx1

lemma Ra_zero (b : ℝ) (E₀ : Mat d) : Ra b X E₀ 0 = matrixEval (filter b) X := by
  rw [Ra_eq]; unfold matrixEval
  refine Finset.sum_congr rfl (fun k _ => ?_); rw [Pk_coeff_zero]

lemma spec01 : ∀ i, hX0.1.eigenvalues i ∈ Set.Icc (0:ℝ) 1 :=
  fun i => ⟨hX0.eigenvalues_nonneg i, hx1 i⟩

lemma Ra_path (b : ℝ) (E₀ : Mat d) (a : ℕ) :
    Ra b X E₀ a = (hX0.1.eigenvectorUnitary : Mat d) *
      OTDUni.Path a hX0.1.eigenvalues (star (hX0.1.eigenvectorUnitary : Mat d) * E₀ *
        (hX0.1.eigenvectorUnitary : Mat d)) (dividedDifference (filter b) a) *
      star (hX0.1.eigenvectorUnitary : Mat d) := by
  rw [← OTDUni.sum_coeff_path hX0.1 (filter b) E₀ a, Ra_eq]
  set U := (hX0.1.eigenvectorUnitary : Mat d)
  have hUU' : U * star U = 1 := Unitary.mul_star_self_of_mem hX0.1.eigenvectorUnitary.2
  simp only [← Matrix.mul_assoc]; rw [hUU', Matrix.one_mul, Matrix.mul_assoc, hUU', Matrix.mul_one]

lemma sqrt_eq : cfc Real.sqrt X = (hX0.1.eigenvectorUnitary : Mat d) *
    diagonal (fun b => ((Real.sqrt (hX0.1.eigenvalues b) : ℝ) : ℂ)) * star (hX0.1.eigenvectorUnitary : Mat d) :=
  OTDUni.cfc_explicit hX0.1 _

theorem mor_Ra (b : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) (a : ℕ) :
    MOR a (fun E₀ _ => Ra b X E₀ a) (uB b a) := by
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h
    refine mor_congr (fun E₀ E₁ => (Ra_zero hX0 hx1 b E₀).symm) (mor_mono (mor_const _) ?_)
    rw [matrixEval_eq_aeval, ← cfc_polynomial _ X hX0.1.isSelfAdjoint]
    refine (OTDUni.opNorm_cfc_le hX0.1 _ zero_le_one (fun i => ?_)).trans (by norm_num [uB])
    obtain ⟨-, -, h3, -⟩ := lemma_2_5 b hb0 hb1
    obtain ⟨a1, a2, -⟩ := h3 _ (spec01 hX0 hx1 i)
    rw [abs_of_nonneg a1]; exact a2
  · exact mor_of_path hX0.1 (spec01 hX0 hx1) (sep_filter_u hb0 hb1 a h) _
      (fun E₀ E₁ => Ra_path hX0 hx1 b E₀ a)

theorem mor_RaS (b : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) (a : ℕ) :
    MOR a (fun E₀ _ => Ra b X E₀ a * cfc Real.sqrt X) (wB b a) := by
  set U := (hX0.1.eigenvectorUnitary : Mat d)
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hX0.1.eigenvectorUnitary.2
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h
    refine mor_congr (fun E₀ E₁ => by rw [Ra_zero hX0 hx1 b E₀]) (mor_mono (mor_const _) ?_)
    rw [matrixEval_eq_aeval, ← cfc_polynomial _ X hX0.1.isSelfAdjoint, cfc_mul2 hX0.1]
    refine (OTDUni.opNorm_cfc_le hX0.1 _ (B := 2^4 * Real.sqrt b) (by positivity) (fun i => ?_)).trans
      (le_of_eq (by simp [wB]))
    obtain ⟨-, -, h3, -⟩ := lemma_2_5 b hb0 hb1
    obtain ⟨a1, -, a3⟩ := h3 _ (spec01 hX0 hx1 i)
    have hx := hX0.eigenvalues_nonneg i
    have h0 := mul_nonneg a1 (Real.sqrt_nonneg (hX0.1.eigenvalues i))
    rw [abs_of_nonneg h0]
    have hsq : ((filter b).eval (hX0.1.eigenvalues i) * Real.sqrt (hX0.1.eigenvalues i))^2 ≤ (2^4 * Real.sqrt b)^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hb0.le]; nlinarith
    exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 hsq
  · have hsep := sep_filter_w hb0 hb1 a h (Fin.last a) (Or.inr rfl)
    refine mor_of_path hX0.1 (spec01 hX0 hx1) hsep _ (fun E₀ E₁ => ?_)
    rw [Ra_path hX0 hx1 b E₀ a, sqrt_eq hX0 hx1]
    have e : (fun x : Fin (a+1) → ℝ => Real.sqrt (x (Fin.last a)) * dividedDifference (filter b) a x) =
        (fun x => dividedDifference (filter b) a x * Real.sqrt (x (Fin.last a))) := by
      funext x; ring
    rw [e, ← Path_weight_right]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]

theorem mor_SRa (b : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) (a : ℕ) :
    MOR a (fun E₀ _ => cfc Real.sqrt X * Ra b X E₀ a) (wB b a) := by
  set U := (hX0.1.eigenvectorUnitary : Mat d)
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hX0.1.eigenvectorUnitary.2
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h
    refine mor_congr (fun E₀ E₁ => by rw [Ra_zero hX0 hx1 b E₀]) (mor_mono (mor_const _) ?_)
    rw [matrixEval_eq_aeval, ← cfc_polynomial _ X hX0.1.isSelfAdjoint, cfc_mul2 hX0.1]
    refine (OTDUni.opNorm_cfc_le hX0.1 _ (B := 2^4 * Real.sqrt b) (by positivity) (fun i => ?_)).trans
      (le_of_eq (by simp [wB]))
    obtain ⟨-, -, h3, -⟩ := lemma_2_5 b hb0 hb1
    obtain ⟨a1, -, a3⟩ := h3 _ (spec01 hX0 hx1 i)
    have hx := hX0.eigenvalues_nonneg i
    have h0 : 0 ≤ Real.sqrt (hX0.1.eigenvalues i) * (filter b).eval (hX0.1.eigenvalues i) :=
      mul_nonneg (Real.sqrt_nonneg _) a1
    rw [abs_of_nonneg h0]
    have hsq : (Real.sqrt (hX0.1.eigenvalues i) * (filter b).eval (hX0.1.eigenvalues i))^2 ≤ (2^4 * Real.sqrt b)^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hb0.le]; nlinarith
    exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 hsq
  · have hsep := sep_filter_w hb0 hb1 a h 0 (Or.inl rfl)
    refine mor_of_path hX0.1 (spec01 hX0 hx1) hsep _ (fun E₀ E₁ => ?_)
    rw [Ra_path hX0 hx1 b E₀ a, sqrt_eq hX0 hx1, ← Path_weight_left]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]

end Rsec

lemma RtL_coeff (b : ℝ) (X Y E₀ E₁ : Mat d) (u : ℕ) :
    (Rt b X E₀ * Lt Y E₁).coeff u = Ra b X E₀ u * Y + (if u = 0 then 0 else Ra b X E₀ (u-1) * E₁) := by
  unfold Lt
  rw [mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C]
  rcases u with _ | u
  · simp [Polynomial.coeff_mul_X_zero, Ra]
  · simp [Polynomial.coeff_mul_X, Ra]

lemma Zt_coeff (b : ℝ) (X Y E₀ E₁ : Mat d) (l : ℕ) :
    (Zt b X Y E₀ E₁).coeff l = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal l,
      (Ra b X E₀ q.1 * Y + (if q.1 = 0 then 0 else Ra b X E₀ (q.1-1) * E₁)) * Ra b X E₀ q.2 := by
  unfold Zt
  rw [Polynomial.coeff_mul]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [RtL_coeff]; rfl

def mB (b : ℝ) (l : ℕ) : ℝ := ∑ q ∈ Finset.HasAntidiagonal.antidiagonal l,
  (wB b q.1 * wB b q.2 + (if q.1 = 0 then 0 else uB b (q.1-1) * uB b q.2))

lemma uB_nonneg {b : ℝ} (hb : 0 < b) (a : ℕ) : 0 ≤ uB b a := by unfold uB; positivity
lemma wB_nonneg {b : ℝ} (hb : 0 < b) (a : ℕ) : 0 ≤ wB b a := by unfold wB; positivity
lemma mB_nonneg {b : ℝ} (hb : 0 < b) (l : ℕ) : 0 ≤ mB b l := by
  unfold mB
  refine Finset.sum_nonneg (fun q _ => add_nonneg (mul_nonneg (wB_nonneg hb _) (wB_nonneg hb _)) ?_)
  split_ifs; exact le_rfl; exact mul_nonneg (uB_nonneg hb _) (uB_nonneg hb _)

theorem mor_Zt {X Y : Mat d} (hX0 : X.PosSemidef) (hx1 : ∀ i, hX0.1.eigenvalues i ≤ 1)
    (hY : Y.IsHermitian) (hlo : lePSD (-X) Y) (hhi : lePSD Y X)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (l : ℕ) :
    MOR l (fun E₀ E₁ => (Zt b X Y E₀ E₁).coeff l) (mB b l) := by
  obtain ⟨J, hJ, hJY⟩ := J_exists hX0 hY hlo hhi
  have hterm : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal l, MOR l
      (fun E₀ E₁ => (Ra b X E₀ q.1 * Y + (if q.1 = 0 then 0 else Ra b X E₀ (q.1-1) * E₁)) * Ra b X E₀ q.2)
      (wB b q.1 * wB b q.2 + (if q.1 = 0 then 0 else uB b (q.1-1) * uB b q.2)) := by
    intro q hq
    have hs : q.1 + q.2 = l := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
    have h1 : MOR l (fun E₀ E₁ => Ra b X E₀ q.1 * Y * Ra b X E₀ q.2) (wB b q.1 * wB b q.2) := by
      have hm := mor_mul (mor_mul (mor_RaS hX0 hx1 b hb0 hb1 q.1) (mor_mono (mor_const J) hJ))
        (mor_SRa hX0 hx1 b hb0 hb1 q.2)
      refine mor_cast (mor_congr (fun E₀ E₁ => ?_) (mor_mono hm (le_of_eq (by ring)))) (by omega)
      rw [← hJY]; simp only [Matrix.mul_assoc]
    by_cases hq0 : q.1 = 0
    · simp only [hq0, if_true, add_zero]
      refine mor_congr (fun E₀ E₁ => ?_) (mor_mono h1 (le_of_eq (by rw [hq0])))
      rw [hq0]
    · simp only [hq0, if_false]
      have h2 : MOR l (fun E₀ E₁ => Ra b X E₀ (q.1-1) * E₁ * Ra b X E₀ q.2) (uB b (q.1-1) * uB b q.2) := by
        have hm := mor_mul (mor_mul (mor_Ra hX0 hx1 b hb0 hb1 (q.1-1)) mor_e1) (mor_Ra hX0 hx1 b hb0 hb1 q.2)
        exact mor_cast (mor_mono hm (le_of_eq (by ring))) (by omega)
      refine mor_congr (fun E₀ E₁ => ?_) (mor_add h1 h2)
      rw [Matrix.add_mul]
  exact mor_congr (fun E₀ E₁ => (Zt_coeff b X Y E₀ E₁ l).symm) (mor_sum _ hterm)

lemma Zt_coeff_zero (b : ℝ) {X : Mat d} (hX0 : X.PosSemidef) (hx1 : ∀ i, hX0.1.eigenvalues i ≤ 1)
    (Y E₀ E₁ : Mat d) :
    (Zt b X Y E₀ E₁).coeff 0 = matrixEval (filter b) X * Y * matrixEval (filter b) X := by
  rw [Zt_coeff]
  simp [Ra_zero hX0 hx1]

lemma eig_le_one_psd {X : Mat d} (hX0 : X.PosSemidef) (hXI : lePSD X 1) (i : Fin d) :
    hX0.1.eigenvalues i ≤ 1 := by
  have hH := hX0.1
  set v := hH.eigenvectorBasis i
  have hv := hH.mulVec_eigenvectorBasis i
  have hn : (star (⇑v) ⬝ᵥ (⇑v : Fin d → ℂ)).re = 1 := by
    have := OTDUni.normsq_eq v
    rw [hH.eigenvectorBasis.orthonormal.1 i] at this
    simpa using this.symm
  have h := OTDUni.re_nonneg_of_psd hXI (⇑v)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv, dotProduct_sub, dotProduct_smul, Complex.sub_re,
    Complex.real_smul, Complex.re_ofReal_mul, hn] at h
  linarith

theorem B2_hob (K : ℕ) (hK : 2 ≤ K) {b s : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (hslo : 2^8 * b ≤ s)
    {X Y : Mat d} (hY : Y.IsHermitian) (hX0 : X.PosSemidef) (hXI : lePSD X 1)
    (hlo : lePSD (-X) Y) (hhi : lePSD Y X) {j : ℕ} (hj : 1 ≤ j) :
    HasOrderedBound j (taylor (G K b s) X Y j)
      (∑ a ∈ Finset.Icc 1 (qScaled K s).natDegree, SBq K s a * Bconv (mB b) a j) := by
  have hx1 := eig_le_one_psd hX0 hXI
  have hs : 0 < s := lt_of_lt_of_le (by positivity) hslo
  set R0 := matrixEval (filter b) X with hR0
  have hR0c : R0 = cfc (fun x => (filter b).eval x) X := by
    rw [hR0, matrixEval_eq_aeval, cfc_polynomial _ X hX0.1.isSelfAdjoint]
  set Z := R0 * Y * R0 with hZdef
  have hR0H : R0.IsHermitian := by rw [hR0c]; exact OTDUni.cfc_herm hX0.1 _
  have hZ : Z.IsHermitian := by
    show (R0 * Y * R0)ᴴ = R0 * Y * R0
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR0H.eq, hY.eq, Matrix.mul_assoc]
  have hZn : opNorm Z ≤ 2^7 * b := by
    rw [hZdef, hR0c]
    refine opNorm_sandwich2 hX0.1 hY hlo hhi _ (by positivity) (fun i => ?_)
    obtain ⟨-, -, h3, -⟩ := lemma_2_5 b hb0 hb1
    exact (h3 _ ⟨hX0.eigenvalues_nonneg i, hx1 i⟩).2.2
  have hspec : ∀ i, hZ.eigenvalues i ∈ Set.Icc (-(s/2)) (s/2) := by
    intro i
    have := (OTDUni.eig_abs_le hZ i).trans hZn
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  have hcomp := taylor_comp (qScaled K s) (fun E₀ E₁ => Zt b X Y E₀ E₁) hZ
    (fun E₀ E₁ => Zt_coeff_zero b hX0 hx1 Y E₀ E₁) hspec (SBq K s)
    (fun a ha _ => sep_qS K hK hs a ha) (mB b) (mB_nonneg hb0)
    (fun l _ => mor_Zt hX0 hx1 hY hlo hhi hb0 hb1 l) hj
  exact hob_congr (fun E₀ E₁ => (taylor_eq K b s X Y j E₀ E₁).symm) hcomp

/-! ### numerics -/

open scoped Nat

/-- `1/(m! n!) ≤ 2^(m+n)/(m+n)!` -/
lemma inv_fact_mul_le (m n : ℕ) :
    1 / ((m ! : ℝ) * (n ! : ℝ)) ≤ 2^(m+n) / ((m+n)! : ℝ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
  rw [Nat.add_sub_cancel_left] at h
  have hc : ((m+n).choose m : ℝ) ≤ 2^(m+n) := by exact_mod_cast Nat.choose_le_two_pow (m+n) m
  have hpos : (0:ℝ) < (m ! : ℝ) * (n ! : ℝ) := by positivity
  rw [div_le_div_iff₀ hpos (by positivity), one_mul]
  have : ((m+n)! : ℝ) = ((m+n).choose m : ℝ) * (m ! : ℝ) * (n ! : ℝ) := by exact_mod_cast h.symm
  rw [this]; nlinarith

/-- `(2a)! ≤ (2a)^a a!` -/
lemma fact_two_le (a : ℕ) : ((2*a)! : ℝ) ≤ (2*a : ℝ)^a * (a ! : ℝ) := by
  have h1 := Nat.factorial_mul_descFactorial (show a ≤ 2*a by omega)
  rw [show 2*a - a = a by omega] at h1
  have h2 := Nat.descFactorial_le_pow (2*a) a
  have : ((2*a)! : ℝ) = (a ! : ℝ) * ((2*a).descFactorial a : ℝ) := by exact_mod_cast h1.symm
  rw [this]
  have h3 : ((2*a).descFactorial a : ℝ) ≤ (2*a : ℝ)^a := by exact_mod_cast h2
  nlinarith [Nat.factorial_pos a]

/-- key inequality behind (76) -/
lemma key76 {K a j : ℕ} (ha : 1 ≤ a) (haK : a ≤ K) (haj : a ≤ j) :
    (K:ℝ)^a * (a:ℝ)^(2*j-2*a) / ((a ! : ℝ) * ((2*j-2*a)! : ℝ)) ≤ 8^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ) := by
  have hch := Nat.choose_mul_factorial_mul_factorial (show 2*a ≤ 2*j by omega)
  have hc : ((2*j).choose (2*a) : ℝ) ≤ 4^j := by
    have := Nat.choose_le_two_pow (2*j) (2*a)
    have h4 : (4:ℝ)^j = 2^(2*j) := by rw [pow_mul]; norm_num
    rw [h4]; exact_mod_cast this
  have hf := fact_two_le a
  have hA : (0:ℝ) < (a ! : ℝ) * ((2*j-2*a)! : ℝ) := by positivity
  rw [div_le_div_iff₀ hA (by positivity)]
  have e : ((2*j)! : ℝ) = ((2*j).choose (2*a) : ℝ) * ((2*a)! : ℝ) * ((2*j-2*a)! : ℝ) := by
    exact_mod_cast hch.symm
  rw [e]
  have hKa : (a:ℝ) ≤ K := by exact_mod_cast haK
  have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
  have hpow : (a:ℝ)^(2*j-a) ≤ (K:ℝ)^(2*j-a) := pow_le_pow_left₀ ha0 hKa _
  have h2a : (2:ℝ)^a ≤ 2^j := pow_le_pow_right₀ (by norm_num) haj
  have e2 : (K:ℝ)^(2*j) = (K:ℝ)^a * (K:ℝ)^(2*j-a) := by rw [← pow_add]; congr 1; omega
  have e3 : (a:ℝ)^(2*j-2*a) * (2*a:ℝ)^a = 2^a * (a:ℝ)^(2*j-a) := by
    rw [mul_pow, ← mul_assoc, mul_comm ((a:ℝ)^(2*j-2*a)) _, mul_assoc, ← pow_add]
    congr 2; omega
  have e8 : (8:ℝ)^j = 4^j * 2^j := by rw [← mul_pow]; norm_num
  calc (K:ℝ)^a * (a:ℝ)^(2*j-2*a) * (((2*j).choose (2*a) : ℝ) * ((2*a)! : ℝ) * ((2*j-2*a)! : ℝ))
      ≤ (K:ℝ)^a * (a:ℝ)^(2*j-2*a) * (4^j * ((2*a : ℝ)^a * (a ! : ℝ)) * ((2*j-2*a)! : ℝ)) := by
        gcongr
    _ = 4^j * (K:ℝ)^a * ((a:ℝ)^(2*j-2*a) * (2*a:ℝ)^a) * ((a ! : ℝ) * ((2*j-2*a)! : ℝ)) := by ring
    _ = 4^j * (K:ℝ)^a * (2^a * (a:ℝ)^(2*j-a)) * ((a ! : ℝ) * ((2*j-2*a)! : ℝ)) := by rw [e3]
    _ ≤ 4^j * (K:ℝ)^a * (2^j * (K:ℝ)^(2*j-a)) * ((a ! : ℝ) * ((2*j-2*a)! : ℝ)) := by gcongr
    _ = 8^j * (K:ℝ)^(2*j) * ((a ! : ℝ) * ((2*j-2*a)! : ℝ)) := by rw [e8, e2]; ring

/-- even part of the binomial expansion -/
lemma binom_even {A : ℝ} (hA : 0 ≤ A) (n : ℕ) :
    ∑ i ∈ Finset.range (n+1), A^(2*i) / (((2*i)! : ℝ) * ((2*n-2*i)! : ℝ)) ≤ (A+1)^(2*n) / ((2*n)! : ℝ) := by
  have hexp : (A+1)^(2*n) / ((2*n)! : ℝ) =
      ∑ p ∈ Finset.range (2*n+1), A^p / ((p ! : ℝ) * ((2*n-p)! : ℝ)) := by
    rw [add_pow, Finset.sum_div]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp' : p ≤ 2*n := by have := Finset.mem_range.1 hp; omega
    have h := Nat.choose_mul_factorial_mul_factorial hp'
    have e : ((2*n).choose p : ℝ) = ((2*n)! : ℝ) / ((p ! : ℝ) * ((2*n-p)! : ℝ)) := by
      rw [eq_div_iff (by positivity)]; exact_mod_cast (by rw [← mul_assoc]; exact h)
    rw [one_pow, mul_one, e]; field_simp
  rw [hexp]
  have himg : ∑ i ∈ Finset.range (n+1), A^(2*i) / (((2*i)! : ℝ) * ((2*n-2*i)! : ℝ)) =
      ∑ p ∈ (Finset.range (n+1)).image (fun i => 2*i), A^p / ((p ! : ℝ) * ((2*n-p)! : ℝ)) := by
    rw [Finset.sum_image (fun i _ j _ h => by omega)]
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
  have := Finset.mem_range.1 hi
  exact Finset.mem_range.2 (by omega)

def Bfun (b c : ℝ) (a j : ℕ) : ℝ :=
  if a ≤ j then b^a * c^j * (a:ℝ)^(2*j-2*a) / ((2*j-2*a)! : ℝ) else 0

lemma Bfun_nonneg {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (a j : ℕ) : 0 ≤ Bfun b c a j := by
  unfold Bfun; split_ifs <;> positivity

theorem Bconv_bound (m : ℕ → ℝ) {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (hm0 : ∀ l, 0 ≤ m l)
    (hm : ∀ l, 1 ≤ l → m l ≤ b * c^l / ((2*l-2)! : ℝ)) :
    ∀ a, 1 ≤ a → ∀ j, Bconv m a j ≤ Bfun b c a j := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base =>
    intro j
    simp only [Bconv]
    rw [Finset.sum_eq_single (j, 0)]
    · simp only [if_true, mul_one]
      unfold Bfun
      by_cases hj : j = 0
      · subst hj; simp
      · rw [if_neg hj, if_pos (by omega)]
        refine (hm j (by omega)).trans (le_of_eq ?_)
        simp
    · intro q hq hne
      have hs : q.1 + q.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
      have : q.2 ≠ 0 := by
        intro h2; apply hne; ext <;> simp <;> omega
      simp [this]
    · intro h; exfalso; exact h (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp))
  | succ a ha ih =>
    intro j
    simp only [Bconv]
    -- termwise bound
    set T : ℕ × ℕ → ℝ := fun q => if 1 ≤ q.1 ∧ a ≤ q.2 then
      (b * c^q.1 / ((2*q.1-2)! : ℝ)) * (b^a * c^q.2 * (a:ℝ)^(2*q.2-2*a) / ((2*q.2-2*a)! : ℝ)) else 0 with hT
    have hle : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal j,
        (if q.1 = 0 then 0 else m q.1) * Bconv m a q.2 ≤ T q := by
      intro q _
      have hB := ih q.2
      have hB0 := Bconv_nonneg hm0 a q.2
      by_cases h1 : q.1 = 0
      · simp only [h1, if_true, zero_mul, hT]; split_ifs <;> first | exact le_rfl | positivity
      · rw [if_neg h1]
        by_cases h2 : a ≤ q.2
        · simp only [hT, if_pos (show 1 ≤ q.1 ∧ a ≤ q.2 from ⟨by omega, h2⟩)]
          unfold Bfun at hB; rw [if_pos h2] at hB
          exact mul_le_mul (hm q.1 (by omega)) hB hB0 (by positivity)
        · unfold Bfun at hB; rw [if_neg h2] at hB
          have : Bconv m a q.2 = 0 := le_antisymm hB hB0
          rw [this, mul_zero]; simp only [hT]; split_ifs <;> first | exact le_rfl | positivity
    refine (Finset.sum_le_sum hle).trans ?_
    unfold Bfun
    by_cases hj : a + 1 ≤ j
    · rw [if_pos hj]
      obtain ⟨n, rfl⟩ : ∃ n, j = a + 1 + n := ⟨j - (a+1), by omega⟩
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      -- only k ∈ [1, n+1] contribute
      have hrw : ∀ k ∈ Finset.range (a + 1 + n + 1), T (k, a + 1 + n - k) =
          if k ∈ Finset.Ico 1 (n+2) then b^(a+1) * c^(a+1+n) *
            ((a:ℝ)^(2*(n+1-k)) / (((2*(n+1-k))! : ℝ) * ((2*k-2)! : ℝ))) else 0 := by
        intro k hk
        simp only [hT, Finset.mem_Ico]
        by_cases hk1 : 1 ≤ k ∧ k < n + 2
        · rw [if_pos ⟨hk1.1, by omega⟩, if_pos hk1]
          have e1 : 2 * (a + 1 + n - k) - 2 * a = 2 * (n + 1 - k) := by omega
          rw [e1]
          have e2 : c^k * c^(a+1+n-k) = c^(a+1+n) := by rw [← pow_add]; congr 1; omega
          field_simp
          rw [← e2]; ring
        · rw [if_neg (by omega), if_neg hk1]
      rw [Finset.sum_congr rfl hrw, ← Finset.sum_filter]
      have hfil : (Finset.range (a + 1 + n + 1)).filter (fun k => k ∈ Finset.Ico 1 (n+2)) = Finset.Ico 1 (n+2) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [hfil, ← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
      simp only [show n + 2 - 1 = n + 1 by omega]
      have hrefl : ∑ i ∈ Finset.range (n+1), (a:ℝ)^(2*(n+1-(1+i))) / (((2*(n+1-(1+i)))! : ℝ) * ((2*(1+i)-2)! : ℝ)) =
          ∑ i ∈ Finset.range (n+1), (a:ℝ)^(2*i) / (((2*i)! : ℝ) * ((2*n-2*i)! : ℝ)) := by
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' := Finset.mem_range.1 hi
        rw [show n + 1 - (1 + (n + 1 - 1 - i)) = i by omega, show 2 * (1 + (n + 1 - 1 - i)) - 2 = 2*n - 2*i by omega]
      rw [hrefl]
      have hbe := binom_even (Nat.cast_nonneg a : (0:ℝ) ≤ a) n
      have e3 : 2 * (a + 1 + n) - 2 * (a + 1) = 2 * n := by omega
      rw [e3]
      have hpos : 0 ≤ b^(a+1) * c^(a+1+n) := by positivity
      calc b^(a+1) * c^(a+1+n) * ∑ i ∈ Finset.range (n+1), (a:ℝ)^(2*i) / (((2*i)! : ℝ) * ((2*n-2*i)! : ℝ))
          ≤ b^(a+1) * c^(a+1+n) * (((a:ℝ)+1)^(2*n) / ((2*n)! : ℝ)) := mul_le_mul_of_nonneg_left hbe hpos
        _ = _ := by push_cast; ring
    · rw [if_neg hj]
      refine le_of_eq (Finset.sum_eq_zero (fun q hq => ?_))
      have hs : q.1 + q.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
      simp only [hT]; rw [if_neg (by omega)]


lemma mB_bound {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (l : ℕ) (hl : 1 ≤ l) :
    mB b l ≤ b * (2^11 / b)^l / ((2*l-2)! : ℝ) := by
  have hsb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb0.le
  rcases Nat.eq_or_lt_of_le hl with h1 | h2
  · subst h1
    unfold mB
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [uB, wB, zero_add, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_zero,
      if_true, Nat.one_ne_zero, if_false, mul_one, div_one]
    norm_num
    field_simp
    nlinarith [hsb]
  · have hl2 : 2 ≤ l := h2
    have hF : (0:ℝ) < ((2*l-2)! : ℝ) := by positivity
    have hterm : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal l,
        wB b q.1 * wB b q.2 + (if q.1 = 0 then 0 else uB b (q.1-1) * uB b q.2) ≤
          (2^(3*l+8) + 2^(3*l+1)) * (b / b^l) / ((2*l-2)! : ℝ) := by
      intro q hq
      have hs : q.1 + q.2 = l := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
      have hw : wB b q.1 * wB b q.2 ≤ 2^(3*l+8) * (b / b^l) / ((2*l-2)! : ℝ) := by
        unfold wB
        have hk1 : 2*l-2 ≤ (2*q.1-1) + (2*q.2-1) := by omega
        have hk2 : (2*q.1-1) + (2*q.2-1) ≤ 2*l := by omega
        have hi := inv_fact_mul_le (2*q.1-1) (2*q.2-1)
        have hfac : ((2*l-2)! : ℝ) ≤ (((2*q.1-1) + (2*q.2-1))! : ℝ) := by
          exact_mod_cast Nat.factorial_le hk1
        have hp2 : (2:ℝ)^((2*q.1-1) + (2*q.2-1)) ≤ 2^(2*l) := pow_le_pow_right₀ (by norm_num) hk2
        have h3 : 1 / (((2*q.1-1)! : ℝ) * ((2*q.2-1)! : ℝ)) ≤ 2^(2*l) / ((2*l-2)! : ℝ) := by
          refine hi.trans ?_
          calc (2:ℝ)^((2*q.1-1) + (2*q.2-1)) / (((2*q.1-1) + (2*q.2-1))! : ℝ)
              ≤ 2^(2*l) / (((2*q.1-1) + (2*q.2-1))! : ℝ) := by gcongr
            _ ≤ 2^(2*l) / ((2*l-2)! : ℝ) := by gcongr
        have e : 2^(q.1+4) * Real.sqrt b / b^q.1 / ((2*q.1-1)! : ℝ) *
            (2^(q.2+4) * Real.sqrt b / b^q.2 / ((2*q.2-1)! : ℝ)) =
            2^(l+8) * (b / b^l) * (1 / (((2*q.1-1)! : ℝ) * ((2*q.2-1)! : ℝ))) := by
          calc 2^(q.1+4) * Real.sqrt b / b^q.1 / ((2*q.1-1)! : ℝ) *
                (2^(q.2+4) * Real.sqrt b / b^q.2 / ((2*q.2-1)! : ℝ))
              = (2^(q.1+4) * 2^(q.2+4)) * (Real.sqrt b * Real.sqrt b) / (b^q.1 * b^q.2) /
                  (((2*q.1-1)! : ℝ) * ((2*q.2-1)! : ℝ)) := by ring
            _ = _ := by
              rw [hsb, ← pow_add, ← pow_add, show q.1+4+(q.2+4) = l+8 by omega, hs]; ring
        rw [e]
        calc 2^(l+8) * (b / b^l) * (1 / (((2*q.1-1)! : ℝ) * ((2*q.2-1)! : ℝ)))
            ≤ 2^(l+8) * (b / b^l) * (2^(2*l) / ((2*l-2)! : ℝ)) := by gcongr
          _ = 2^(3*l+8) * (b / b^l) / ((2*l-2)! : ℝ) := by
            rw [show 3*l+8 = (l+8) + 2*l by ring, pow_add]; ring
      have hu : (if q.1 = 0 then 0 else uB b (q.1-1) * uB b q.2) ≤ 2^(3*l+1) * (b / b^l) / ((2*l-2)! : ℝ) := by
        split_ifs with h0
        · positivity
        · unfold uB
          have hk : 2*(q.1-1) + 2*q.2 = 2*l-2 := by omega
          have hi := inv_fact_mul_le (2*(q.1-1)) (2*q.2)
          rw [hk] at hi
          have e : 2^(q.1-1+2) / b^(q.1-1) / ((2*(q.1-1))! : ℝ) * (2^(q.2+2) / b^q.2 / ((2*q.2)! : ℝ)) =
              2^(l+3) * (b / b^l) * (1 / (((2*(q.1-1))! : ℝ) * ((2*q.2)! : ℝ))) := by
            have hb' : b^l = b^(q.1-1) * b^q.2 * b := by
              rw [← pow_add, ← pow_succ]; congr 1; omega
            have h2' : (2:ℝ)^(l+3) = 2^(q.1-1+2) * 2^(q.2+2) := by
              rw [← pow_add]; congr 1; omega
            rw [hb', h2']; field_simp
          rw [e]
          calc 2^(l+3) * (b / b^l) * (1 / (((2*(q.1-1))! : ℝ) * ((2*q.2)! : ℝ)))
              ≤ 2^(l+3) * (b / b^l) * (2^(2*l-2) / ((2*l-2)! : ℝ)) := by gcongr
            _ = 2^(3*l+1) * (b / b^l) / ((2*l-2)! : ℝ) := by
              rw [show 3*l+1 = (l+3) + (2*l-2) by omega, pow_add]; ring
      have := add_le_add hw hu
      rw [← add_div, ← add_mul] at this; exact this
    unfold mB
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    have hl1 : ((l:ℝ) + 1) ≤ 2^l := by
      have : l + 1 ≤ 2^l := Nat.lt_two_pow_self
      exact_mod_cast this
    have h2p : (2:ℝ)^(3*l+8) + 2^(3*l+1) ≤ 2^(3*l+9) := by
      have e1 : (2:ℝ)^(3*l+9) = 2^(3*l+1) * 256 := by rw [show 3*l+9 = (3*l+1)+8 by ring, pow_add]; norm_num
      have e2 : (2:ℝ)^(3*l+8) = 2^(3*l+1) * 128 := by rw [show 3*l+8 = (3*l+1)+7 by ring, pow_add]; norm_num
      rw [e1, e2]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (3*l+1)]
    have hfin : ((l:ℝ) + 1) * (2^(3*l+8) + 2^(3*l+1)) ≤ 2^(11*l) := by
      calc ((l:ℝ) + 1) * (2^(3*l+8) + 2^(3*l+1)) ≤ 2^l * 2^(3*l+9) := by
            gcongr
        _ = 2^(4*l+9) := by rw [← pow_add]; ring_nf
        _ ≤ 2^(11*l) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : b * (2^11 / b)^l / ((2*l-2)! : ℝ) = 2^(11*l) * (b / b^l) / ((2*l-2)! : ℝ) := by
      rw [div_pow, ← pow_mul]; ring
    rw [e]
    have hpos : 0 ≤ (b / b^l) / ((2*l-2)! : ℝ) := by positivity
    calc ((l + 1 : ℕ) : ℝ) * ((2^(3*l+8) + 2^(3*l+1)) * (b / b^l) / ((2*l-2)! : ℝ))
        = (((l:ℝ) + 1) * (2^(3*l+8) + 2^(3*l+1))) * ((b / b^l) / ((2*l-2)! : ℝ)) := by push_cast; ring
      _ ≤ 2^(11*l) * ((b / b^l) / ((2*l-2)! : ℝ)) := mul_le_mul_of_nonneg_right hfin hpos
      _ = _ := by ring

lemma qS_natDegree (K : ℕ) (hK : 2 ≤ K) (s : ℝ) : (qScaled K s).natDegree ≤ K := by
  unfold qScaled
  refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
  have h1 := (lemma_2_3 K hK).1
  have h2 : (C s⁻¹ * X : Polynomial ℝ).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
  calc (q K).natDegree * (C s⁻¹ * X : Polynomial ℝ).natDegree ≤ K * 1 := Nat.mul_le_mul h1 h2
    _ = K := by ring

lemma SBq_nonneg (K : ℕ) {s : ℝ} (hs : 0 < s) (a : ℕ) : 0 ≤ SBq K s a := by
  unfold SBq; split_ifs <;> positivity

theorem B2_final (K : ℕ) (hK : 2 ≤ K) {b s : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hslo : 2^8 * b ≤ s) (hshi : s ≤ 2^9 * b) {j : ℕ} (hj : 1 ≤ j) :
    ∑ a ∈ Finset.Icc 1 (qScaled K s).natDegree, SBq K s a * Bconv (mB b) a j ≤
      2^10 * K * b * (2^16 * (K:ℝ)^2 / b)^j / ((2*j).factorial : ℝ) := by
  set c := (2:ℝ)^11 / b with hc
  have hc0 : 0 < c := by positivity
  have hs : 0 < s := lt_of_lt_of_le (by positivity) hslo
  have hKr : (2:ℝ) ≤ K := by exact_mod_cast hK
  set X0 := b * (8 * c)^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ) with hX0
  have hX00 : 0 ≤ X0 := by positivity
  have hN := qS_natDegree K hK s
  have hterm : ∀ a ∈ Finset.Icc 1 (qScaled K s).natDegree,
      SBq K s a * Bconv (mB b) a j ≤ 2^13 * (1/16)^a * X0 := by
    intro a ha
    have ha' := Finset.mem_Icc.1 ha
    have haK : a ≤ K := ha'.2.trans hN
    have hB := Bconv_bound (mB b) hb0 hc0 (mB_nonneg hb0) (fun l hl => mB_bound hb0 hb1 l hl) a ha'.1 j
    have hSB0 := SBq_nonneg K hs a
    refine (mul_le_mul_of_nonneg_left hB hSB0).trans ?_
    unfold Bfun
    by_cases haj : a ≤ j
    · rw [if_pos haj]
      have hk := key76 ha'.1 haK haj
      have e8 : (8 * c)^j = 8^j * c^j := mul_pow _ _ _
      by_cases ha1 : a = 1
      · subst ha1
        simp only [SBq, if_true, pow_one, one_pow, mul_one, Nat.factorial_one, Nat.cast_one, one_mul] at hk ⊢
        rw [hX0, e8]
        calc 16 * (K:ℝ) * (b * c^j / ((2*j-2)! : ℝ)) = 16 * b * c^j * ((K:ℝ) / ((2*j-2)! : ℝ)) := by ring
          _ ≤ 16 * b * c^j * (8^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ)) := by gcongr
          _ ≤ 2^13 * (1/16) * (b * (8^j * c^j) * (K:ℝ)^(2*j) / ((2*j)! : ℝ)) := by
            have hP : 0 ≤ b * c^j * (8^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ)) := by positivity
            have e : 2^13 * (1/16) * (b * (8^j * c^j) * (K:ℝ)^(2*j) / ((2*j)! : ℝ)) =
                512 * (b * c^j * (8^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ))) := by ring
            rw [e]; linarith
      · simp only [SBq, if_neg ha1]
        have hr : 16 * b * s⁻¹ ≤ 1/16 := by
          rw [← div_eq_mul_inv, div_le_iff₀ hs]; nlinarith
        have hr0 : 0 ≤ 16 * b * s⁻¹ := by positivity
        have hKa : (K:ℝ)^(a-1) ≤ (K:ℝ)^a / 2 := by
          rw [le_div_iff₀ (by norm_num)]
          have : (K:ℝ)^a = (K:ℝ)^(a-1) * K := by rw [← pow_succ]; congr 1; omega
          rw [this]; nlinarith [pow_pos (show (0:ℝ) < K by linarith) (a-1)]
        have e : s * (s⁻¹)^a * (16^a * (K:ℝ)^(a-1) / (a ! : ℝ)) *
            (b^a * c^j * (a:ℝ)^(2*j-2*a) / ((2*j-2*a)! : ℝ)) =
            s * (16 * b * s⁻¹)^a * c^j * ((K:ℝ)^(a-1) * (a:ℝ)^(2*j-2*a) / ((a ! : ℝ) * ((2*j-2*a)! : ℝ))) := by
          rw [mul_pow, mul_pow]; field_simp
        rw [e]
        have hq : (K:ℝ)^(a-1) * (a:ℝ)^(2*j-2*a) / ((a ! : ℝ) * ((2*j-2*a)! : ℝ)) ≤
            (1/2) * (8^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ)) := by
          calc (K:ℝ)^(a-1) * (a:ℝ)^(2*j-2*a) / ((a ! : ℝ) * ((2*j-2*a)! : ℝ))
              ≤ ((K:ℝ)^a / 2) * (a:ℝ)^(2*j-2*a) / ((a ! : ℝ) * ((2*j-2*a)! : ℝ)) := by gcongr
            _ = (1/2) * ((K:ℝ)^a * (a:ℝ)^(2*j-2*a) / ((a ! : ℝ) * ((2*j-2*a)! : ℝ))) := by ring
            _ ≤ (1/2) * (8^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ)) := by gcongr
        have hpw : (16 * b * s⁻¹)^a ≤ (1/16)^a := pow_le_pow_left₀ hr0 hr a
        rw [hX0, e8]
        calc s * (16 * b * s⁻¹)^a * c^j * ((K:ℝ)^(a-1) * (a:ℝ)^(2*j-2*a) / ((a ! : ℝ) * ((2*j-2*a)! : ℝ)))
            ≤ (2^9 * b) * (1/16)^a * c^j * ((1/2) * (8^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ))) := by
              gcongr
          _ ≤ 2^13 * (1/16)^a * (b * (8^j * c^j) * (K:ℝ)^(2*j) / ((2*j)! : ℝ)) := by
              have hP : 0 ≤ (1/16:ℝ)^a * c^j * b * (8^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ)) := by positivity
              have e1 : (2^9 * b) * (1/16)^a * c^j * ((1/2) * (8^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ))) =
                  2^8 * ((1/16:ℝ)^a * c^j * b * (8^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ))) := by ring
              have e2 : 2^13 * (1/16)^a * (b * (8^j * c^j) * (K:ℝ)^(2*j) / ((2*j)! : ℝ)) =
                  2^13 * ((1/16:ℝ)^a * c^j * b * (8^j * (K:ℝ)^(2*j) / ((2*j)! : ℝ))) := by ring
              rw [e1, e2]; linarith
    · rw [if_neg haj, mul_zero]; positivity
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hg : ∑ a ∈ Finset.Icc 1 (qScaled K s).natDegree, (1/16:ℝ)^a ≤ 1/15 := by
    rw [show Finset.Icc 1 (qScaled K s).natDegree = Finset.Ico 1 ((qScaled K s).natDegree + 1) by
      ext; simp]
    refine (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans (by norm_num)
  have h1 : 2^13 * ∑ a ∈ Finset.Icc 1 (qScaled K s).natDegree, (1/16:ℝ)^a ≤ 2^10 := by
    nlinarith
  have hfin : X0 ≤ b * (2^16 * (K:ℝ)^2 / b)^j / ((2*j).factorial : ℝ) := by
    rw [hX0]
    have e1 : b * (8 * c)^j * (K:ℝ)^(2*j) = b * (2^14 * (K:ℝ)^2 / b)^j := by
      have : (8 * c) * (K:ℝ)^2 = 2^14 * (K:ℝ)^2 / b := by rw [hc]; field_simp; ring
      rw [← this, mul_pow, pow_mul]; ring
    rw [e1]
    have h4 : (2^14 * (K:ℝ)^2 / b)^j ≤ (2^16 * (K:ℝ)^2 / b)^j :=
      pow_le_pow_left₀ (by positivity) (by gcongr <;> norm_num) j
    gcongr
  calc (2^13 * ∑ a ∈ Finset.Icc 1 (qScaled K s).natDegree, (1/16:ℝ)^a) * X0 ≤ 2^10 * X0 :=
        mul_le_mul_of_nonneg_right h1 hX00
    _ ≤ 2^10 * (b * (2^16 * (K:ℝ)^2 / b)^j / ((2*j).factorial : ℝ)) := by gcongr
    _ ≤ 2^10 * K * b * (2^16 * (K:ℝ)^2 / b)^j / ((2*j).factorial : ℝ) := by
        have hY : 0 ≤ b * (2^16 * (K:ℝ)^2 / b)^j / ((2*j).factorial : ℝ) := by positivity
        have e : 2^10 * K * b * (2^16 * (K:ℝ)^2 / b)^j / ((2*j).factorial : ℝ) =
            2^10 * K * (b * (2^16 * (K:ℝ)^2 / b)^j / ((2*j).factorial : ℝ)) := by ring
        rw [e]; nlinarith

end OTDB2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
open OptimalTraceDistance.Estimation in
theorem solution (d K : ℕ) (hd : 0 < d) (hK : 2 ≤ K)
    (b s : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hslo : (2 : ℝ)^8*b ≤ s) (hshi : s ≤ (2 : ℝ)^9*b)
    (X Y : Mat d) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hX0 : X.PosSemidef) (hXI : lePSD X 1) (hlo : lePSD (-X) Y) (hhi : lePSD Y X) :
  let r := exprPoly (filter b) (exprVar d false)
  let g := traceExpr (exprPoly (qScaled K s) (exprMul (exprMul r (exprVar d true)) r))
  ∀ j : ℕ, 1 ≤ j → HasOrderedBound j (taylor g X Y j)
    ((2 : ℝ)^10*K*b * ((2 : ℝ)^16*(K:ℝ)^2/b)^j / ((2*j).factorial : ℝ)) := by
  intro r g j hj
  have h1 := OTDB2.B2_hob K hK hb hb1 hslo hY hX0 hXI hlo hhi hj
  have h2 := OTDB2.B2_final K hK hb hb1 hslo hshi hj
  exact OTDB2.hob_mono h1 h2
