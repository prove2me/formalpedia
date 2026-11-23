-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T08:04:32.369544+00:00
-- url     : https://prove2.me/submissions/a28c32d1-b712-4c6b-b6c1-a7a5eca0177c

import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_B_1
import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_2_3
import Theorems.Thm_OptimalTraceDistance_Estimation_proposition_4_3
import Theorems.Thm_OptimalTraceDistance_Estimation_proposition_2_1

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

open scoped Nat
namespace OTDNum44

lemma add_pow_ge {x S : ℝ} (hx : 0 ≤ x) (hS : 0 ≤ S) : ∀ a : ℕ, 1 ≤ a → x^a + S^a ≤ (x + S)^a
  | 0, h => by omega
  | 1, _ => by simp
  | (a+2), _ => by
    have ih := add_pow_ge hx hS (a+1) (by omega)
    calc x^(a+2) + S^(a+2) ≤ (x + S) * (x^(a+1) + S^(a+1)) := by
          rw [pow_succ x, pow_succ S]
          nlinarith [pow_nonneg hx (a+1), pow_nonneg hS (a+1)]
      _ ≤ (x + S) * (x + S)^(a+1) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (x + S)^(a+2) := by ring

lemma sum_pow_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (a : ℕ) (ha : 1 ≤ a) :
    ∑ i ∈ s, c i ^ a ≤ (∑ i ∈ s, c i) ^ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_pow (by omega : a ≠ 0)]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h1 := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    have h2 := add_pow_ge (hc i (Finset.mem_insert_self i s))
      (Finset.sum_nonneg (fun j hj => hc j (Finset.mem_insert_of_mem hj))) a ha
    linarith

/-- (51): Σ w^j/(j!)^a ≤ exp(a w^{1/a}) over any range -/
lemma series_bound (w : ℝ) (hw : 0 ≤ w) (a : ℕ) (ha : 1 ≤ a) (S : Finset ℕ) :
    ∑ j ∈ S, w^j / ((j ! : ℝ))^a ≤ Real.exp (a * w ^ (1 / (a:ℝ))) := by
  set u := w ^ (1 / (a:ℝ)) with hu
  have hu0 : 0 ≤ u := by positivity
  have hua : u ^ a = w := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hw, one_div_mul_cancel (by positivity), Real.rpow_one]
  have e : ∀ j, w^j / ((j ! : ℝ))^a = (u^j / j !)^a := by
    intro j; rw [div_pow, ← pow_mul, mul_comm j a, pow_mul, hua]
  simp only [e]
  refine (sum_pow_le S _ (fun j _ => by positivity) a ha).trans ?_
  rw [show a * u = u * a by ring, Real.exp_mul]
  have hS : ∑ j ∈ S, u^j / (j ! : ℝ) ≤ Real.exp u := by
    have hsub : S ⊆ Finset.range (S.sup id + 1) := by
      intro j hj; simp; have := Finset.le_sup (f := id) hj; simp at this; omega
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)) ?_
    exact Real.sum_le_exp_of_nonneg hu0 _
  rw [Real.rpow_natCast]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => by positivity)) hS a

lemma choose_inv_le {n j : ℕ} (h : 2 * j ≤ n) (hn : 0 < n) :
    ((n.choose j : ℕ) : ℝ)⁻¹ ≤ (j ! : ℝ) * (2 / n)^j := by
  have h1 : ((n / 2 : ℝ))^j ≤ (n.descFactorial j : ℝ) := by
    have := Nat.pow_sub_le_descFactorial n j
    have h2 : (n / 2 : ℝ) ≤ ((n + 1 - j : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      have : (2 * j : ℝ) ≤ n := by exact_mod_cast h
      push_cast; linarith
    calc ((n / 2 : ℝ))^j ≤ ((n + 1 - j : ℕ) : ℝ)^j := pow_le_pow_left₀ (by positivity) h2 j
      _ ≤ _ := by exact_mod_cast this
  have h3 : (n.descFactorial j : ℝ) = (j ! : ℝ) * n.choose j := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n j
  have hc : (0:ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos (by omega)
  have hf : (0:ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  rw [h3] at h1
  rw [inv_le_iff_one_le_mul₀ hc]
  calc (1:ℝ) = (j ! : ℝ) * (2/n)^j * ((n/2)^j / j !) := by
        rw [div_pow, div_pow]; field_simp
    _ ≤ (j ! : ℝ) * (2/n)^j * n.choose j := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ hf]; linarith

lemma fact_two_ge (j : ℕ) : 2^j * ((j ! : ℝ))^2 ≤ ((2*j) ! : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j+1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have h0 : (0:ℝ) ≤ 2 * ((j:ℝ) + 1)^2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left ih h0
    have h2 : 2 * ((j:ℝ) + 1)^2 ≤ (2 * j + 1 + 1) * (2 * j + 1) := by nlinarith
    have h3 : 0 ≤ (((2 * j) ! : ℕ) : ℝ) := by positivity
    calc (2:ℝ)^(j+1) * (((j:ℝ) + 1) * j !)^2 = 2 * ((j:ℝ) + 1)^2 * (2^j * ((j ! : ℝ))^2) := by ring
      _ ≤ 2 * ((j:ℝ) + 1)^2 * ((2*j) ! : ℝ) := h1
      _ ≤ (2 * j + 1 + 1) * (2 * j + 1) * ((2*j) ! : ℝ) := mul_le_mul_of_nonneg_right h2 h3
      _ = _ := by ring

lemma prod_le (β : ℝ) (hβ : 0 < β) (j : ℕ) :
    ∏ l ∈ Finset.range j, (1 + (l:ℝ) * β) ≤ 2^j * (1 + (j * β)^j) := by
  calc ∏ l ∈ Finset.range j, (1 + (l:ℝ) * β) ≤ ∏ _l ∈ Finset.range j, (1 + (j:ℝ) * β) := by
        apply Finset.prod_le_prod (fun l _ => by positivity)
        intro l hl; simp at hl
        have : (l:ℝ) ≤ j := by exact_mod_cast hl.le
        nlinarith
    _ = (1 + j * β)^j := by simp
    _ ≤ (2 * max 1 (j * β))^j := pow_le_pow_left₀ (by positivity)
        (by have := le_max_left 1 ((j:ℝ) * β); have := le_max_right 1 ((j:ℝ) * β); linarith) j
    _ = 2^j * (max 1 (j * β))^j := by ring
    _ ≤ 2^j * (1 + (j * β)^j) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total 1 ((j:ℝ) * β) with h | h
        · rw [max_eq_right h]; linarith [pow_nonneg (by positivity : (0:ℝ) ≤ j * β) j]
        · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (by positivity : (0:ℝ) ≤ j * β) j]


lemma pow_le_two_pow (j : ℕ) : (j:ℝ) ≤ 2^j := by
  have := Nat.lt_two_pow_self (n := j); exact_mod_cast this.le

lemma jpow_le (j : ℕ) : ((j:ℝ))^j ≤ 3^j * (j ! : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (x := (j:ℝ)) (by positivity) j
  have he : Real.exp j ≤ 3^j := by
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) (by have := Real.exp_one_lt_d9; norm_num at this; linarith) j
  have hf : (0:ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hf] at h
  nlinarith


lemma abstract_bound {Cinv F G J u v P β : ℝ} (j : ℕ) (hG : 0 < G) (hJ : 0 < J) (hF : F = J * G)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hβ : 0 ≤ β) (hC0 : 0 ≤ Cinv)
    (hC : Cinv ≤ F * u^j) (hP0 : 0 ≤ P) (hP : P ≤ 2^j * (1 + (J * β)^j)) (hJ2 : J ≤ 2^j)
    (hJp : J^j ≤ 3^j * F) :
    Cinv * (256^j * v / F^2) * (P / G) ≤ (1024 * u)^j * v / F^2 + (3072 * u * β)^j * v / F := by
  have hF0 : 0 < F := by rw [hF]; positivity
  have hG' : 1 / G = J / F := by rw [hF]; field_simp
  calc Cinv * (256^j * v / F^2) * (P / G)
      ≤ (F * u^j) * (256^j * v / F^2) * ((2^j * (1 + (J * β)^j)) / G) := by gcongr
    _ = (512 * u)^j * v * J / F^2 + (512 * u)^j * v * J^j * β^j * (J / F) / F := by
        rw [div_eq_mul_one_div _ G, hG']
        simp only [mul_pow]
        rw [show (512:ℝ)^j = 2^j * 256^j by rw [← mul_pow]; norm_num]
        field_simp
        try ring
    _ ≤ (512 * u)^j * v * 2^j / F^2 + (512 * u)^j * v * (3^j * F) * β^j * (2^j / F) / F := by
        gcongr
    _ = (1024 * u)^j * v / F^2 + (3072 * u * β)^j * v / F := by
        simp only [mul_pow]
        rw [show (1024:ℝ)^j = 512^j * 2^j by rw [← mul_pow]; norm_num,
          show (3072:ℝ)^j = 512^j * 3^j * 2^j by rw [← mul_pow, ← mul_pow]; norm_num]
        field_simp

lemma term_main {K β : ℝ} (hK : 0 < K) (hβ : 0 < β) {n j : ℕ} (hj : 2 ≤ j) (hjn : 2 * j ≤ n) (hn : 0 < n) :
    ((n.choose j : ℕ) : ℝ)⁻¹ * (16^j * K^(j-1) / (j ! : ℝ))^2 *
      ((∏ l ∈ Finset.range j, (1 + (l:ℝ) * β)) / ((j-1) ! : ℝ)) ≤
      1 / K^2 * ((2048 * K^2 / n)^j / ((j ! : ℝ))^2 + (6144 * β * K^2 / n)^j / (j ! : ℝ)) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hfac : (j ! : ℝ) = (j:ℝ) * ((j-1) ! : ℝ) := by
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp [Nat.factorial_succ]
  have hab := abstract_bound (Cinv := ((n.choose j : ℕ) : ℝ)⁻¹) (F := (j ! : ℝ)) (G := ((j-1) ! : ℝ))
    (J := (j:ℝ)) (u := 2 / n) (v := K^(2*j-2)) (P := ∏ l ∈ Finset.range j, (1 + (l:ℝ) * β)) (β := β) j
    (by exact_mod_cast Nat.factorial_pos _) (by exact_mod_cast (by omega : 0 < j)) hfac (by positivity)
    (by positivity) hβ.le (by positivity) (choose_inv_le hjn hn)
    (Finset.prod_nonneg (fun l _ => by positivity)) (prod_le β hβ j) (pow_le_two_pow j) (jpow_le j)
  have hsq : (16^j * K^(j-1) / (j ! : ℝ))^2 = 256^j * K^(2*j-2) / (j ! : ℝ)^2 := by
    rw [div_pow, mul_pow, ← pow_mul, ← pow_mul]
    rw [show (16:ℝ)^(j*2) = 256^j by rw [mul_comm j 2, pow_mul]; norm_num]
    congr 3; omega
  rw [hsq]
  refine hab.trans (le_of_eq ?_)
  have hK2 : K^(2*j-2) = K^(2*j) / K^2 := by
    rw [eq_div_iff (by positivity), ← pow_add]; congr 1; omega
  rw [hK2]
  simp only [div_pow, mul_pow, ← pow_mul]
  rw [show (2048:ℝ)^j = 1024^j * 2^j by rw [← mul_pow]; norm_num,
    show (6144:ℝ)^j = 3072^j * 2^j by rw [← mul_pow]; norm_num]
  field_simp


lemma exp_tail (x : ℝ) (hx : 0 ≤ x) (D : ℕ) :
    ∑ j ∈ Finset.Icc 2 D, x^j / (j ! : ℝ) ≤ Real.exp x - 1 - x := by
  have h := Real.sum_le_exp_of_nonneg hx (D+2)
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
    Nat.factorial_one] at h
  have hsub : ∑ j ∈ Finset.Icc 2 D, x^j / (j ! : ℝ) ≤ ∑ i ∈ Finset.range D, x^(i+1+1) / ((i+1+1) ! : ℝ) := by
    rw [show (Finset.Icc 2 D) = (Finset.range D).map ⟨fun i => i + 2, fun a b h => by simpa using h⟩ ∩ Finset.Icc 2 D by
      ext j; simp only [Finset.mem_inter, Finset.mem_map, Finset.mem_range, Finset.mem_Icc,
        Function.Embedding.coeFn_mk]
      constructor
      · intro hj; obtain ⟨h1, h2⟩ := hj; exact ⟨⟨j - 2, by omega, show j - 2 + 2 = j by omega⟩, h1, h2⟩
      · intro h; exact h.2]
    refine (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun j _ _ => by positivity)).trans
      (le_of_eq ?_)
    rw [Finset.sum_map]; rfl
  linarith

lemma sum_bound2 {K β : ℝ} (hK : 0 < K) (hβ : 0 < β) {n D : ℕ} (hD : 2 * D ≤ n) (hn : 0 < n) :
    ∑ j ∈ Finset.Icc 2 D, ((n.choose j : ℕ) : ℝ)⁻¹ * (16^j * K^(j-1) / (j ! : ℝ))^2 *
      ((∏ l ∈ Finset.range j, (1 + (l:ℝ) * β)) / ((j-1) ! : ℝ)) ≤
      1 / K^2 * (Real.exp (92 * K / Real.sqrt n) + Real.exp (6144 * β * K^2 / n)) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ j ∈ Finset.Icc 2 D, ((n.choose j : ℕ) : ℝ)⁻¹ * (16^j * K^(j-1) / (j ! : ℝ))^2 *
      ((∏ l ∈ Finset.range j, (1 + (l:ℝ) * β)) / ((j-1) ! : ℝ)) ≤
      1 / K^2 * ((2048 * K^2 / n)^j / ((j ! : ℝ))^2 + (6144 * β * K^2 / n)^j / (j ! : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact term_main hK hβ hj.1 (by omega) hn
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
  · have h := series_bound (2048 * K^2 / n) (by positivity) 2 (by norm_num) (Finset.Icc 2 D)
    refine h.trans (Real.exp_le_exp.2 ?_)
    rw [show (1 / ((2:ℕ):ℝ)) = (1/2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hK.le]
    have hs : Real.sqrt 2048 ≤ 46 := by
      rw [show (46:ℝ) = Real.sqrt (46^2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
    push_cast
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hsn]
    nlinarith [hs, hK]
  · have h := series_bound (6144 * β * K^2 / n) (by positivity) 1 (by norm_num) (Finset.Icc 2 D)
    simp only [Nat.cast_one, div_one, Real.rpow_one, one_mul, pow_one] at h
    exact h

lemma sum_bound1 {K : ℝ} (hK : 0 < K) {n D : ℕ} (hD : 2 * D ≤ n) (hn : 0 < n) :
    ∑ j ∈ Finset.Icc 2 D, ((n.choose j : ℕ) : ℝ)⁻¹ * (16^j * K^(j-1) / (j ! : ℝ))^2 *
      ((∏ l ∈ Finset.range j, (1 + (l:ℝ) * 1)) / ((j-1) ! : ℝ)) ≤
      2 / K^2 * (Real.exp (6144 * K^2 / n) - 1 - 6144 * K^2 / n) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  set x := 6144 * K^2 / n with hx
  have hx0 : 0 ≤ x := by positivity
  have hterm : ∀ j ∈ Finset.Icc 2 D, ((n.choose j : ℕ) : ℝ)⁻¹ * (16^j * K^(j-1) / (j ! : ℝ))^2 *
      ((∏ l ∈ Finset.range j, (1 + (l:ℝ) * 1)) / ((j-1) ! : ℝ)) ≤ 2 / K^2 * (x^j / (j ! : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h := term_main hK one_pos hj.1 (by omega : 2 * j ≤ n) hn
    refine h.trans ?_
    have hf : (1:ℝ) ≤ (j ! : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
    have h1 : (2048 * K^2 / n)^j ≤ x^j := pow_le_pow_left₀ (by positivity)
      (by rw [hx]; gcongr; norm_num) j
    have h2 : (2048 * K^2 / n)^j / ((j ! : ℝ))^2 ≤ x^j / (j ! : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc (2048 * K^2 / n)^j * (j ! : ℝ) ≤ x^j * (j ! : ℝ) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ x^j * (j ! : ℝ) * (j ! : ℝ) := le_mul_of_one_le_right (by positivity) hf
        _ = x^j * (j ! : ℝ)^2 := by ring
    rw [show 6144 * 1 * K^2 / (n:ℝ) = x by rw [hx]; ring]
    have : 1 / K^2 * ((2048 * K^2 / n)^j / ((j ! : ℝ))^2 + x^j / (j ! : ℝ)) ≤
        1 / K^2 * (x^j / (j ! : ℝ) + x^j / (j ! : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 le_rfl) (by positivity)
    refine this.trans (le_of_eq ?_)
    ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (exp_tail x hx0 D) (by positivity)

end OTDNum44

open OptimalTraceDistance.Estimation OTDUni OTDNum44 in
theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d →
  ∀ ρ σ : Mat d, Density ρ → Density σ → ∀ Q : Mat d, projector Q →
  ∀ K n : ℕ, 2 ≤ K → 2*K ≤ n →
    polynomialVariance (substituteCompression Q (univariate d K)) n ρ σ ≤
      (Real.exp (C*(K : ℝ)^2/n)-1)/(K : ℝ)^2 ∧
    ∀ β : ℝ, 0 < β → opNorm (compress Q (plus ρ σ)) ≤ β →
      polynomialVariance (substituteCompression Q (univariate d K)) n ρ σ ≤
        1/(n : ℝ) + (Real.exp (C*K/Real.sqrt n) +
          Real.exp (C*β*(K : ℝ)^2/n))/(K : ℝ)^2 := by
  refine ⟨12288, by norm_num, fun d hd ρ σ hρ hσ Q hQ K n hK hn => ?_⟩
  set g := univariate d K with hgdef
  set D := expressionDegree g with hDdef
  have hD : D ≤ K := deg_univariate K hK
  have hn0 : 0 < n := by omega
  have hDn : D ≤ n := by omega
  have hD2 : 2 * D ≤ n := by omega
  have hKr : (0:ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  obtain ⟨p1, -⟩ := proposition_2_1 d hd
  obtain ⟨-, -, -, -, hmin, hcomp⟩ := p1 ρ σ hρ hσ
  obtain ⟨hSpsd, -, -, hStr⟩ := hcomp Q hQ
  have hQH : Qᴴ = Q := hQ.1.eq
  have hMH : (minus ρ σ).IsHermitian := by
    unfold minus Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hρ.1.1.eq, hσ.1.1.eq]; simp
  set Y := compress Q (minus ρ σ) with hYdef
  have hY : Y.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hYdef, compress, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQH, hMH.eq, Matrix.mul_assoc]
  have hYn : opNorm Y ≤ 1/2 := (opNorm_QXQ hQH hQ.2 _).trans hmin
  have hspec : ∀ a, hY.eigenvalues a ∈ Set.Icc (-(1/2 : ℝ)) (1/2) := by
    intro a
    have := (eig_abs_le hY a).trans hYn
    rw [abs_le] at this
    exact ⟨this.1, this.2⟩
  set M : ℕ → ℝ := fun j => if j = 1 then 1 else 16^j * (K:ℝ)^(j-1) / (j.factorial : ℝ) with hMdef
  have hM : ∀ j ∈ Finset.Icc 1 D, HasOrderedBound j
      (OptimalTraceDistance.Estimation.taylor g (compress Q (plus ρ σ)) Y j) (M j) := by
    intro j hj
    by_cases h1 : j = 1
    · subst h1
      simp only [hMdef, if_true]
      refine uni_rep1 hY _ zero_le_one (fun a => ?_)
      have hx := hspec a
      exact ((lemma_2_3 K hK).2.2.2.1 _ ⟨by linarith [hx.1], by linarith [hx.2]⟩).1
    · simp only [hMdef, if_neg h1]
      exact uni_rep (Finset.mem_Icc.1 hj).1 hY hspec (sep_q K j hK (by have := (Finset.mem_Icc.1 hj).1; omega)) _
  have key : ∀ β : ℝ, 0 < β → opNorm (compress Q (plus ρ σ)) ≤ β →
      polynomialVariance (substituteCompression Q g) n ρ σ ≤ 1 / (n:ℝ) +
        ∑ j ∈ Finset.Icc 2 D, ((n.choose j : ℕ) : ℝ)⁻¹ * (16^j * (K:ℝ)^(j-1) / (j.factorial : ℝ))^2 *
          ((∏ l ∈ Finset.range j, (1 + (l:ℝ) * β)) / ((j-1).factorial : ℝ)) := by
    intro β hβ hb
    have h43 := proposition_4_3 d hd ρ σ hρ hσ Q hQ β hβ hb g (real_univariate K) M hM n hn0 hDn
    refine h43.trans ?_
    set f : ℕ → ℝ := fun j => ((n.choose j : ℕ) : ℝ)⁻¹ * (M j)^2 * cycleFactor β j with hf
    have hf0 : ∀ j, 0 ≤ f j := by
      intro j; simp only [hf]
      refine mul_nonneg (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (sq_nonneg _)) ?_
      unfold cycleFactor; exact div_nonneg (Finset.prod_nonneg (fun l _ => by positivity)) (by positivity)
    have hsub : Finset.Icc 1 D ⊆ insert 1 (Finset.Icc 2 D) := by
      intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_insert, Finset.mem_Icc]; omega
    have h1 : ∑ j ∈ Finset.Icc 1 D, f j ≤ f 1 + ∑ j ∈ Finset.Icc 2 D, f j := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hf0 j)).trans (le_of_eq ?_)
      rw [Finset.sum_insert (by simp)]
    refine h1.trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))
    · simp only [hf, hMdef, if_true, one_pow, mul_one, Nat.choose_one_right]
      unfold cycleFactor
      simp
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj2 := (Finset.mem_Icc.1 hj).1
      simp only [hf, hMdef, if_neg (by omega : j ≠ 1)]
      rfl
  constructor
  · -- β = 1
    have hb1 : opNorm (compress Q (plus ρ σ)) ≤ 1 := (opNorm_le_trace hSpsd).trans hStr
    have h := key 1 one_pos hb1
    have hs := sum_bound1 hKr hD2 hn0
    refine h.trans ?_
    set x := 6144 * (K:ℝ)^2 / n with hx
    have hx0 : 0 ≤ x := by positivity
    have hnx : 1 / (n:ℝ) ≤ x / (K:ℝ)^2 := by
      rw [hx, div_div, div_le_div_iff₀ hnr (by positivity)]
      nlinarith [sq_nonneg (K:ℝ)]
    have hexp : 2 * Real.exp x - 2 ≤ Real.exp (2 * x) - 1 := by
      have : Real.exp (2 * x) = Real.exp x ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
      nlinarith [sq_nonneg (Real.exp x - 1)]
    have hfin : (Real.exp (12288 * (K:ℝ)^2 / n) - 1) / (K:ℝ)^2 = (Real.exp (2 * x) - 1) / (K:ℝ)^2 := by
      rw [hx]; congr 2; ring
    rw [hfin]
    have hK2 : 0 < (K:ℝ)^2 := by positivity
    calc 1 / (n:ℝ) + ∑ j ∈ Finset.Icc 2 D, ((n.choose j : ℕ) : ℝ)⁻¹ * (16^j * (K:ℝ)^(j-1) / (j.factorial : ℝ))^2 *
          ((∏ l ∈ Finset.range j, (1 + (l:ℝ) * 1)) / ((j-1).factorial : ℝ))
        ≤ x / (K:ℝ)^2 + 2 / (K:ℝ)^2 * (Real.exp x - 1 - x) := add_le_add hnx hs
      _ = (2 * Real.exp x - 2 - x) / (K:ℝ)^2 := by field_simp; ring
      _ ≤ (Real.exp (2 * x) - 1) / (K:ℝ)^2 := by
          apply div_le_div_of_nonneg_right _ hK2.le; linarith
  · intro β hβ hb
    have h := key β hβ hb
    have hs := sum_bound2 hKr hβ hD2 hn0
    refine h.trans (add_le_add le_rfl (hs.trans ?_))
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
    have hA : Real.exp (92 * (K:ℝ) / Real.sqrt n) ≤ Real.exp (12288 * K / Real.sqrt n) := by
      apply Real.exp_le_exp.2
      rw [div_le_div_iff_of_pos_right hsn]; nlinarith
    have hB : Real.exp (6144 * β * (K:ℝ)^2 / n) ≤ Real.exp (12288 * β * (K:ℝ)^2 / n) := by
      apply Real.exp_le_exp.2
      rw [div_le_div_iff_of_pos_right hnr]; nlinarith [mul_pos hβ (pow_pos hKr 2)]
    calc 1 / (K:ℝ)^2 * (Real.exp (92 * (K:ℝ) / Real.sqrt n) + Real.exp (6144 * β * (K:ℝ)^2 / n))
        = (Real.exp (92 * (K:ℝ) / Real.sqrt n) + Real.exp (6144 * β * (K:ℝ)^2 / n)) / (K:ℝ)^2 := by ring
      _ ≤ (Real.exp (12288 * K / Real.sqrt n) + Real.exp (12288 * β * (K:ℝ)^2 / n)) / (K:ℝ)^2 :=
        div_le_div_of_nonneg_right (add_le_add hA hB) (by positivity)
