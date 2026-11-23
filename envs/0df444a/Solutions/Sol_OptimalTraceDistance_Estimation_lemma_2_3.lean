-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:06:39.076659+00:00
-- url     : https://prove2.me/submissions/9fb7a972-1e45-4267-ba0e-db9d70bdc24c

import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_B_1

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

open OptimalTraceDistance.Estimation OTDJackson

theorem solution : ∀ K : ℕ, 2 ≤ K →
  (q K).natDegree ≤ K ∧ (∀ x : ℝ, (q K).eval (-x) = (q K).eval x) ∧
  (q K).eval 0 = 0 ∧
  (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(q K).derivative.eval x| ≤ 1 ∧
    |(q K).eval x - abs x| ≤ 64/(K : ℝ)) ∧
  (∀ j : ℕ, 2 ≤ j → j ≤ K → ∀ x ∈ Set.Icc (-(1/2) : ℝ) (1/2),
    |((Polynomial.derivative^[j]) (q K)).eval x| ≤ (64 : ℝ)^j * (K : ℝ)^(j-1)) ∧
  IntegrableOn (fun x => |sign x - (q K).derivative.eval x|) (Set.Icc (-1 : ℝ) 1) ∧
  (∫ x in (-1 : ℝ)..1, |sign x - (q K).derivative.eval x|) ≤ 64/(K : ℝ) ∧
  (∀ x ∈ Set.Icc (-1 : ℝ) 1,
    |x| * |sign x - (q K).derivative.eval x| ≤ 64/(K : ℝ)) := by
  intro K hK
  obtain ⟨hM1, hKM⟩ := Mr_facts K hK
  set Mr := ((K/2+1 : ℕ) : ℝ) with hMr
  have hMpos : 0 < Mr := by linarith
  have hKpos : (0:ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hE : ∀ x, |sign x - (q K).derivative.eval x| = Efun K x := fun x => by
    rw [abs_sub_comm, q_derivative]; rfl
  have half := int_Efun_half K hK
  have h8 : 8 / Mr ≤ 16 / (K:ℝ) := by
    rw [div_le_div_iff₀ hMpos hKpos]; linarith
  have h1664 : 16 / (K:ℝ) ≤ 64 / K := by
    rw [div_le_div_iff₀ hKpos hKpos]; nlinarith
  refine ⟨q_natDegree K (by omega), q_even K, q_eval_zero K, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨by rw [q_derivative]; exact D_abs_le K hK hx.1 hx.2, ?_⟩
    have e : (q K).eval x - |x| = ∫ t in (0:ℝ)..x, ((jacksonDerivative K).eval t - sign t) := by
      rw [intervalIntegral.integral_sub ((Polynomial.continuous _).intervalIntegrable _ _)
        (sign_intInt _ _), q_ftc, int_sign]
    rw [e]
    have hfi : ∀ a b, IntervalIntegrable (fun t => (jacksonDerivative K).eval t - sign t) volume a b :=
      fun a b => ((Polynomial.continuous _).intervalIntegrable a b).sub (sign_intInt a b)
    rcases le_or_gt 0 x with h0 | h0
    · calc _ ≤ ∫ t in (0:ℝ)..x, Efun K t := intervalIntegral.abs_integral_le_integral_abs h0
        _ ≤ ∫ t in (0:ℝ)..1, Efun K t := intervalIntegral.integral_mono_interval le_rfl h0 hx.2
            (Filter.Eventually.of_forall (fun t => abs_nonneg _)) (Efun_intInt K _ _)
        _ ≤ 64 / K := by linarith
    · rw [intervalIntegral.integral_symm, abs_neg]
      calc _ ≤ ∫ t in x..0, Efun K t := intervalIntegral.abs_integral_le_integral_abs h0.le
        _ ≤ ∫ t in (-1:ℝ)..0, Efun K t := intervalIntegral.integral_mono_interval hx.1 h0.le le_rfl
            (Filter.Eventually.of_forall (fun t => abs_nonneg _)) (Efun_intInt K _ _)
        _ ≤ 64 / K := by
            rw [int_Efun_negHalf]
            linarith
  · intro j hj hjK x hx
    obtain ⟨r, rfl⟩ : ∃ r, j = r + 1 := ⟨j - 1, by omega⟩
    rw [Function.iterate_succ_apply, q_derivative]
    refine (D_deriv_bound K hK r (by omega) hx).trans ?_
    simp only [Nat.add_sub_cancel]
    gcongr
    · norm_num
  · have : (fun x => |sign x - (q K).derivative.eval x|) = Efun K := funext hE
    rw [this, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp (Efun_intInt K _ _)
  · simp only [hE]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (Efun_intInt K _ _)
      (Efun_intInt K _ _), int_Efun_negHalf]
    have h32 : 16 / (K:ℝ) + 16 / K ≤ 64 / K := by
      rw [← add_div, div_le_div_iff₀ hKpos hKpos]; nlinarith
    have half' : ∫ x in (0:ℝ)..1, Efun K x ≤ 8 / Mr := half
    linarith
  · intro x hx
    rw [hE]
    by_cases hx0 : x = 0
    · subst hx0; simp; positivity
    have hxa : 0 < |x| := abs_pos.mpr hx0
    have h2 := Efun_le2 K hK hx.1 hx.2
    have h3 : Efun K x ≤ 32 / (Mr * |x|)^3 := D_sign_le K hK hx.1 hx.2 hx0
    have h64 : 8 / Mr ≤ 64 / K := h8.trans (by rw [div_le_div_iff₀ hKpos hKpos]; nlinarith)
    by_cases hc : Mr * |x| ≤ 2
    · calc |x| * Efun K x ≤ |x| * 2 := mul_le_mul_of_nonneg_left h2 hxa.le
        _ ≤ 8 / Mr := by rw [le_div_iff₀ hMpos]; nlinarith
        _ ≤ 64 / K := h64
    · push Not at hc
      calc |x| * Efun K x ≤ |x| * (32 / (Mr * |x|)^3) := mul_le_mul_of_nonneg_left h3 hxa.le
        _ = 32 / (Mr * (Mr * |x|)^2) := by field_simp
        _ ≤ 32 / (Mr * 4) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            exact mul_le_mul_of_nonneg_left (by nlinarith) hMpos.le
        _ = 8 / Mr := by ring
        _ ≤ 64 / K := h64
