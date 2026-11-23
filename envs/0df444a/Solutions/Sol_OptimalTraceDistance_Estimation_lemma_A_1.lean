-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T08:25:35.102526+00:00
-- url     : https://prove2.me/submissions/3126e6d6-644c-440b-a8ab-be66e4cd9d98

import Theorems.Thm_OptimalTraceDistance_Estimation_lemma_2_3

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

/-- Sharp form of (61): `|x| |sign x - q_K'(x)| ≤ 16/K` on `[-1,1]`. -/
lemma q_sharp (K : ℕ) (hK : 2 ≤ K) {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |x| * |sign x - (q K).derivative.eval x| ≤ 16 / (K : ℝ) := by
  have hKr : (0:ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  rcases eq_or_ne x 0 with rfl | hx
  · simp; positivity
  set M : ℕ := K/2+1 with hM
  have hMr : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have h2M : (K:ℝ) ≤ 2 * M := by exact_mod_cast (by omega : K ≤ 2 * M)
  rw [q_derivative, abs_sub_comm]
  have hb1 := D_sign_le K hK hx1 hx2 hx
  have hb2 : |(jacksonDerivative K).eval x - sign x| ≤ 2 := by
    have := D_abs_le K hK hx1 hx2
    have hs : |sign x| ≤ 1 := by unfold sign; split_ifs <;> norm_num
    exact (abs_sub _ _).trans (by linarith)
  have hu : 0 < |x| := abs_pos.mpr hx
  have h8 : |x| * |(jacksonDerivative K).eval x - sign x| ≤ 8 / M := by
    rcases le_or_gt ((M:ℝ) * |x|) 4 with hle | hlt
    · calc |x| * |(jacksonDerivative K).eval x - sign x| ≤ |x| * 2 :=
            mul_le_mul_of_nonneg_left hb2 hu.le
        _ ≤ 8 / M := by rw [le_div_iff₀ hMr]; nlinarith
    · calc |x| * |(jacksonDerivative K).eval x - sign x| ≤ |x| * (32 / ((M:ℝ) * |x|)^3) :=
            mul_le_mul_of_nonneg_left hb1 hu.le
        _ = 32 / ((M:ℝ) * ((M:ℝ) * |x|)^2) := by field_simp
        _ ≤ 8 / M := by
            rw [div_le_div_iff₀ (by positivity) hMr]
            nlinarith [mul_pos hMr hMr]
  refine h8.trans ?_
  rw [div_le_div_iff₀ hMr hKr]; nlinarith

end OTDJackson

open scoped ComplexOrder
namespace OTDA1
open Matrix OptimalTraceDistance.Estimation

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

lemma trace_cfc (f : ℝ → ℝ) : (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [cfc_explicit hA, Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem (U_mem hA),
    Matrix.one_mul, trace_diagonal]

lemma cfc_congr' {f g : ℝ → ℝ} (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) :
    cfc f A = cfc g A := by
  rw [cfc_explicit hA, cfc_explicit hA]; simp only [h]

lemma cfc_mul' (f g : ℝ → ℝ) : cfc f A * cfc g A = cfc (fun t => f t * g t) A := by
  rw [cfc_explicit hA, cfc_explicit hA, cfc_explicit hA]
  set U := (hA.eigenvectorUnitary : Mat d)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (U_mem hA)
  calc U * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) * star U *
        (U * diagonal (fun i => ((g (hA.eigenvalues i) : ℝ) : ℂ)) * star U)
      = U * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) * (star U * U) *
          diagonal (fun i => ((g (hA.eigenvalues i) : ℝ) : ℂ)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]; push_cast; rfl

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

section congruence
variable {d : ℕ}

lemma matrixEval_eq_aeval (p : Polynomial ℝ) (B : Mat d) : matrixEval p B = Polynomial.aeval B p := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, matrixEval, Polynomial.sum_def]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [show ((p.coeff k : ℝ) : ℂ) • B ^ k = (p.coeff k : ℝ) • B ^ k from
    (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm]

lemma traceError_eq (K : ℕ) (s : ℝ) {A : Mat d} (hA : A.IsHermitian) :
    traceError K s A = ∑ k, (|hA.eigenvalues k| - (qScaled K s).eval (hA.eigenvalues k)) := by
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  have e : Aᴴ * A = cfc (fun t : ℝ => t * t) A := by
    rw [hA.eq, ← cfc_mul' hA, cfc_id' ℝ A hA.isSelfAdjoint]
  unfold traceError tr absMat
  rw [trace_sub, Complex.sub_re, e, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) A hA.isSelfAdjoint
    ((hfin.image _).continuousOn _) (hfin.continuousOn _), trace_cfc hA, matrixEval_eq_aeval,
    ← cfc_polynomial (qScaled K s) A hA.isSelfAdjoint, trace_cfc hA, Complex.re_sum, Complex.re_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Function.comp, Complex.ofReal_re]
  rw [← sq, Real.sqrt_sq_eq_abs]

lemma trace_matrixEval_re (p : Polynomial ℝ) {A : Mat d} (hA : A.IsHermitian) :
    (matrixEval p A).trace.re = ∑ i, p.eval (hA.eigenvalues i) := by
  rw [matrixEval_eq_aeval, ← cfc_polynomial p A hA.isSelfAdjoint, trace_cfc hA, Complex.re_sum]
  simp

lemma traceNorm_eq {A : Mat d} (hA : A.IsHermitian) :
    QAlgorithms.traceNorm A = ∑ i, |hA.eigenvalues i| := by
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  have e : Aᴴ * A = cfc (fun t : ℝ => t * t) A := by
    rw [hA.eq, ← cfc_mul' hA, cfc_id' ℝ A hA.isSelfAdjoint]
  unfold QAlgorithms.traceNorm
  rw [e, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) A hA.isSelfAdjoint
    ((hfin.image _).continuousOn _) (hfin.continuousOn _), trace_cfc hA, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Function.comp, Complex.ofReal_re]
  rw [← sq, Real.sqrt_sq_eq_abs]

/-- trace duality: `|Re tr(L M)| ≤ ‖L‖₁ ‖M‖` for Hermitian `L`. -/
lemma trace_dual {L : Mat d} (hL : L.IsHermitian) (M : Mat d) :
    |(L * M).trace.re| ≤ QAlgorithms.traceNorm L * opNorm M := by
  set V := (hL.eigenvectorUnitary : Mat d) with hV
  have hVV : star V * V = 1 := Unitary.star_mul_self_of_mem (U_mem hL)
  have hLe : L = V * diagonal (fun i => ((hL.eigenvalues i : ℝ) : ℂ)) * star V := by
    have := cfc_explicit hL (fun t => t)
    rwa [cfc_id' ℝ L hL.isSelfAdjoint] at this
  set D := diagonal (fun i => ((hL.eigenvalues i : ℝ) : ℂ)) with hD
  have htr : (L * M).trace = ∑ i, ((hL.eigenvalues i : ℝ) : ℂ) * (star V * M * V) i i := by
    have e1 : (L * M).trace = (V * D * star V * M).trace := by rw [← hLe]
    have e2 : V * D * star V * M = V * (D * (star V * M)) := by simp only [Matrix.mul_assoc]
    rw [e1, e2, Matrix.trace_mul_comm, Matrix.mul_assoc, hD]
    simp only [Matrix.trace, Matrix.diagonal_mul, Matrix.diag]
  have hcol : ∀ i, (star V * M * V) i i =
      star (fun j => V j i) ⬝ᵥ (M *ᵥ fun j => V j i) := by
    intro i
    simp only [Matrix.mul_apply, dotProduct, mulVec, Finset.sum_mul, Pi.star_apply,
      Matrix.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  have hnorm : ∀ i, (star (fun j => V j i) ⬝ᵥ (fun j => V j i)).re = 1 := by
    intro i
    have : star (fun j => V j i) ⬝ᵥ (fun j => V j i) = (star V * V) i i := by
      simp [dotProduct, Matrix.mul_apply, Matrix.star_apply]
    rw [this, hVV]; simp
  rw [htr, Complex.re_sum, traceNorm_eq hL, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [Complex.re_ofReal_mul, abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := quad_le_opNorm M (fun j => V j i)
  rw [hnorm, mul_one, ← hcol] at this
  simpa only [Matrix.mul_assoc] using this

lemma trace_cycle_aux (U L : Mat d) (m a : ℕ) :
    (U ^ m * (L * U + U * L) * U ^ a).trace = 2 * (L * U ^ (m + a + 1)).trace := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  have h1 : (U ^ m * (L * U) * U ^ a).trace = (L * U ^ (m + a + 1)).trace := by
    have e : U ^ m * (L * U) * U ^ a = U ^ m * (L * U ^ (a + 1)) := by
      rw [pow_succ']; simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_add]
    congr 3; ring
  have h2 : (U ^ m * (U * L) * U ^ a).trace = (L * U ^ (m + a + 1)).trace := by
    have e : U ^ m * (U * L) * U ^ a = U ^ (m + 1) * (L * U ^ a) := by
      rw [pow_succ]; simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_add]
    congr 3; ring
  rw [h1, h2]; ring

end congruence

section calc_sec
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma hasDerivAt_pow' (F : ℝ → Mat d) (F' : Mat d) (t : ℝ) (hF : HasDerivAt F F' t) :
    ∀ k : ℕ, HasDerivAt (fun u => F u ^ k)
      (∑ m ∈ Finset.range k, F t ^ m * F' * F t ^ (k - 1 - m)) t
  | 0 => by simpa using hasDerivAt_const t (1 : Mat d)
  | k+1 => by
    have h := (hasDerivAt_pow' F F' t hF k).fun_mul hF
    simp only [← pow_succ] at h
    refine h.congr_deriv ?_
    rw [Finset.sum_range_succ, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm' := Finset.mem_range.1 hm
      rw [show k + 1 - 1 - m = (k - 1 - m) + 1 by omega, pow_succ]; simp only [Matrix.mul_assoc]
    · simp

lemma hasDerivAt_trace (F : ℝ → Mat d) (F' : Mat d) (t : ℝ) (hF : HasDerivAt F F' t) :
    HasDerivAt (fun u => (F u).trace.re) (F'.trace.re) t := by
  let T : Mat d →L[ℝ] ℝ :=
    (Complex.reCLM.comp (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin d) ℝ ℂ)))
  have := T.hasFDerivAt.comp_hasDerivAt t hF
  exact this

lemma exp_eq_cfc {L : Mat d} (hL : L.IsHermitian) (t : ℝ) :
    NormedSpace.exp (t • L) = cfc (fun x => Real.exp (t * x)) L := by
  have hsa : IsSelfAdjoint (t • L) := (IsSelfAdjoint.all t).smul hL.isSelfAdjoint
  rw [← CFC.real_exp_eq_normedSpace_exp hsa]
  exact (cfc_comp_smul t Real.exp L).symm

lemma aeval_Xderiv (p : Polynomial ℝ) (A : Mat d) :
    Polynomial.aeval A (Polynomial.X * Polynomial.derivative p) =
      ∑ k ∈ Finset.range (p.natDegree + 1), (p.coeff k * k) • A ^ k := by
  rw [Polynomial.aeval_eq_sum_range' (n := p.natDegree + 1)]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    rcases k with _ | k
    · simp
    · rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]; push_cast; ring
  · by_cases h0 : p.natDegree = 0
    · rw [Polynomial.derivative_of_natDegree_zero h0]; simp
    · have h1 := Polynomial.natDegree_derivative_lt h0
      have h2 := Polynomial.natDegree_mul_le (p := Polynomial.X) (q := Polynomial.derivative p)
      have h3 : (Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := Polynomial.natDegree_X_le
      omega

theorem poly_congr (p : Polynomial ℝ) {U Λ : Mat d} (hU : U.IsHermitian) {s : ℝ}
    (hUs : opNorm U ≤ s) (hΛ : Λ.PosDef) (hΛ1 : ∀ i, hΛ.1.eigenvalues i ≤ 1) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Set.Icc (-s) s, |x * (Polynomial.derivative p).eval x| ≤ B) :
    |(Polynomial.aeval (Λ * U * Λ) p).trace.re - (Polynomial.aeval U p).trace.re| ≤
      2 * QAlgorithms.traceNorm (logMat Λ) * B := by
  have hΛH := hΛ.1
  set L := logMat Λ with hLdef
  have hLH : L.IsHermitian := cfc_herm hΛH Real.log
  set T := QAlgorithms.traceNorm L with hT
  have hT0 : 0 ≤ T := by
    rw [hT, traceNorm_eq hLH]; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  set D : ℝ → Mat d := fun t => NormedSpace.exp (t • L) with hDdef
  have hfin : (spectrum ℝ Λ).Finite := Matrix.finite_real_spectrum
  have hDc : ∀ t, D t = cfc (fun x => Real.exp (t * Real.log x)) Λ := by
    intro t
    show NormedSpace.exp (t • L) = _
    rw [exp_eq_cfc hLH t, hLdef, logMat, ← cfc_comp (fun x => Real.exp (t * x)) Real.log Λ
      hΛH.isSelfAdjoint ((hfin.image _).continuousOn _) (hfin.continuousOn _)]
    rfl
  have hpos := hΛ.eigenvalues_pos
  have hD0 : D 0 = 1 := by simp [hDdef]
  have hD1 : D 1 = Λ := by
    rw [hDc 1, cfc_congr' hΛH (g := fun x => x) (fun i => by simp [Real.exp_log (hpos i)]),
      cfc_id' ℝ Λ hΛH.isSelfAdjoint]
  have hDH : ∀ t, (D t).IsHermitian := fun t => by rw [hDc t]; exact cfc_herm hΛH _
  have hDn : ∀ t, 0 ≤ t → opNorm (D t) ≤ 1 := by
    intro t ht; rw [hDc t]
    refine opNorm_cfc_le hΛH _ zero_le_one (fun a => ?_)
    have hl : Real.log (hΛH.eigenvalues a) ≤ 0 := Real.log_nonpos (hpos a).le (hΛ1 a)
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos ht hl)
  have hLD : ∀ t, L * D t = D t * L := by
    intro t; rw [hDc t, hLdef, logMat, cfc_mul' hΛH, cfc_mul' hΛH]; congr 1; funext x; ring
  set Ut : ℝ → Mat d := fun t => D t * U * D t with hUt
  have hUtH : ∀ t, (Ut t).IsHermitian := by
    intro t
    show (D t * U * D t)ᴴ = D t * U * D t
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, (hDH t).eq, hU.eq, Matrix.mul_assoc]
  have hUtn : ∀ t, 0 ≤ t → opNorm (Ut t) ≤ s := by
    intro t ht
    have h1 := hDn t ht
    have hU0 := opNorm_nonneg' U
    have hD0' := opNorm_nonneg' (D t)
    calc opNorm (Ut t) ≤ opNorm (D t) * opNorm U * opNorm (D t) :=
          (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) hD0')
      _ ≤ 1 * s * 1 := by
          gcongr
          · exact mul_nonneg zero_le_one (hU0.trans hUs)
      _ = s := by ring
  have hderU : ∀ t, HasDerivAt Ut (L * Ut t + Ut t * L) t := by
    intro t
    have hD : HasDerivAt D (L * D t) t := hasDerivAt_exp_smul_const' L t
    have h1 := (hD.fun_mul (hasDerivAt_const t U)).fun_mul hD
    refine h1.congr_deriv ?_
    simp only [hUt, mul_zero, add_zero, Matrix.mul_assoc]
    rw [← hLD t]
  set N := p.natDegree + 1
  set f : ℝ → ℝ := fun t => (Polynomial.aeval (Ut t) p).trace.re with hf
  set f' : ℝ → ℝ := fun t =>
    2 * (L * Polynomial.aeval (Ut t) (Polynomial.X * Polynomial.derivative p)).trace.re with hf'
  have hderf : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    have hs : HasDerivAt (fun u => ∑ k ∈ Finset.range N, p.coeff k • Ut u ^ k)
        (∑ k ∈ Finset.range N, p.coeff k • ∑ m ∈ Finset.range k,
          Ut t ^ m * (L * Ut t + Ut t * L) * Ut t ^ (k - 1 - m)) t :=
      HasDerivAt.fun_sum (fun k _ => (hasDerivAt_pow' Ut _ t (hderU t) k).const_smul (p.coeff k))
    have ht := hasDerivAt_trace _ _ t hs
    have hfe : f = fun u => (∑ k ∈ Finset.range N, p.coeff k • Ut u ^ k).trace.re := by
      funext u; simp only [hf, Polynomial.aeval_eq_sum_range]; rfl
    rw [hfe]
    refine ht.congr_deriv ?_
    simp only [hf', aeval_Xderiv, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
      Matrix.trace_smul, Complex.re_sum, Complex.smul_re, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hm : ∀ m ∈ Finset.range k, (Ut t ^ m * (L * Ut t + Ut t * L) * Ut t ^ (k - 1 - m)).trace.re =
        2 * (L * Ut t ^ k).trace.re := by
      intro m hm
      have hm' := Finset.mem_range.1 hm
      rw [trace_cycle_aux, show m + (k - 1 - m) + 1 = k by omega]
      simp
    rw [Finset.sum_congr rfl hm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [smul_eq_mul]; ring
  have hbound : ∀ x ∈ Set.Ico (0:ℝ) 1, ‖f' x‖ ≤ 2 * T * B := by
    intro x hx
    have hM : Polynomial.aeval (Ut x) (Polynomial.X * Polynomial.derivative p) =
        cfc (fun y => (Polynomial.X * Polynomial.derivative p).eval y) (Ut x) :=
      (cfc_polynomial _ _ (hUtH x).isSelfAdjoint).symm
    have hMn : opNorm (Polynomial.aeval (Ut x) (Polynomial.X * Polynomial.derivative p)) ≤ B := by
      rw [hM]
      refine opNorm_cfc_le (hUtH x) _ hB0 (fun a => ?_)
      rw [Polynomial.eval_mul, Polynomial.eval_X]
      refine hB _ ?_
      have := (eig_abs_le (hUtH x) a).trans (hUtn x hx.1)
      rw [abs_le] at this; exact this
    rw [Real.norm_eq_abs]
    simp only [hf']
    rw [abs_mul, abs_two]
    have := trace_dual hLH (Polynomial.aeval (Ut x) (Polynomial.X * Polynomial.derivative p))
    calc 2 * |(L * Polynomial.aeval (Ut x) (Polynomial.X * Polynomial.derivative p)).trace.re|
        ≤ 2 * (T * opNorm (Polynomial.aeval (Ut x) (Polynomial.X * Polynomial.derivative p))) := by
          gcongr
      _ ≤ 2 * (T * B) := by gcongr
      _ = 2 * T * B := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := f') (a := 0) (b := 1)
    (fun x _ => (hderf x).hasDerivWithinAt) hbound 1 ⟨zero_le_one, le_rfl⟩
  have h1 : f 1 = (Polynomial.aeval (Λ * U * Λ) p).trace.re := by simp only [hf, hUt, hD1]
  have h0 : f 0 = (Polynomial.aeval U p).trace.re := by
    simp only [hf, hUt, hD0, Matrix.one_mul, Matrix.mul_one]
  rw [h1, h0, Real.norm_eq_abs] at hmvt
  simpa using hmvt

end calc_sec

section final
variable {d : ℕ}

lemma qS_eval (K : ℕ) {s : ℝ} (x : ℝ) : (qScaled K s).eval x = s * (q K).eval (x / s) := by
  simp only [qScaled, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_X]
  rw [div_eq_inv_mul]

lemma qScaled_deriv (K : ℕ) {s : ℝ} (hs : s ≠ 0) (t : ℝ) :
    (qScaled K s).derivative.eval t = (q K).derivative.eval (t/s) := by
  simp only [qScaled, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.derivative_X, mul_one, Polynomial.eval_X]
  rw [div_eq_inv_mul]; field_simp

lemma eig_le_one {Λ : Mat d} (hΛ : Λ.PosDef) (hΛI : lePSD Λ 1) (i : Fin d) :
    hΛ.1.eigenvalues i ≤ 1 := by
  have hΛH := hΛ.1
  set v := hΛH.eigenvectorBasis i
  have hv := hΛH.mulVec_eigenvectorBasis i
  have hn : (star (⇑v) ⬝ᵥ (⇑v : Fin d → ℂ)).re = 1 := by
    have := normsq_eq v
    rw [hΛH.eigenvectorBasis.orthonormal.1 i] at this
    simpa using this.symm
  have h := re_nonneg_of_psd hΛI (⇑v)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv, dotProduct_sub, dotProduct_smul, Complex.sub_re,
    Complex.real_smul, Complex.re_ofReal_mul, hn] at h
  linarith

/-- splitting of the trace error against a second polynomial width `n` -/
lemma split_err (K n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) {A : Mat d} (hA : A.IsHermitian)
    (hAs : opNorm A ≤ s) :
    |traceError K s A - (Polynomial.aeval A (qScaled n s - qScaled K s)).trace.re| ≤
      d * (64 * s / n) := by
  rw [traceError_eq K s hA, ← cfc_polynomial _ A hA.isSelfAdjoint, trace_cfc hA, Complex.re_sum,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ i ∈ Finset.univ, |(|hA.eigenvalues i| - (qScaled K s).eval (hA.eigenvalues i)) -
      (((qScaled n s - qScaled K s).eval (hA.eigenvalues i) : ℝ) : ℂ).re| ≤ 64 * s / n := by
    intro i _
    set x := hA.eigenvalues i
    have hx := (eig_abs_le hA i).trans hAs
    have hy : x / s ∈ Set.Icc (-1:ℝ) 1 := by
      rw [abs_le] at hx
      constructor
      · rw [le_div_iff₀ hs]; linarith
      · rw [div_le_iff₀ hs]; linarith
    have h23 := ((lemma_2_3 n hn).2.2.2.1 (x / s) hy).2
    rw [Complex.ofReal_re, Polynomial.eval_sub, qS_eval n x]
    have e : |x| - (qScaled K s).eval x - (s * (q n).eval (x / s) - (qScaled K s).eval x) =
        -(s * ((q n).eval (x / s) - abs (x / s))) := by
      rw [abs_div, abs_of_pos hs]; field_simp; ring
    rw [e, abs_neg, abs_mul, abs_of_pos hs]
    calc s * abs ((q n).eval (x / s) - abs (x / s)) ≤ s * (64 / n) :=
          mul_le_mul_of_nonneg_left h23 hs.le
      _ = 64 * s / n := by ring
  refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
  simp

theorem lemma_A_1_proof (d K : ℕ) (hd : 0 < d) (hK : 2 ≤ K)
    (s : ℝ) (hs : 0 < s) (U Λ : Mat d) (hU : U.IsHermitian) (hUs : opNorm U ≤ s)
    (hΛ : Λ.PosDef) (hΛI : lePSD Λ 1) :
    |traceError K s (Λ * U * Λ) - traceError K s U| ≤
      (2 : ℝ)^5*s/K * QAlgorithms.traceNorm (logMat Λ) := by
  have hΛH := hΛ.1
  have hΛ1 := eig_le_one hΛ hΛI
  have hLH : (logMat Λ).IsHermitian := cfc_herm hΛH Real.log
  set T := QAlgorithms.traceNorm (logMat Λ) with hT
  have hT0 : 0 ≤ T := by
    rw [hT, traceNorm_eq hLH]; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hKr : (0:ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hΛn : opNorm Λ ≤ 1 := by
    have : cfc (fun x : ℝ => x) Λ = Λ := cfc_id' ℝ Λ hΛH.isSelfAdjoint
    rw [← this]
    refine opNorm_cfc_le hΛH _ zero_le_one (fun a => ?_)
    rw [abs_of_pos (hΛ.eigenvalues_pos a)]; exact hΛ1 a
  have hVH : (Λ * U * Λ).IsHermitian := by
    show (Λ * U * Λ)ᴴ = Λ * U * Λ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hΛH.eq, hU.eq, Matrix.mul_assoc]
  have hVs : opNorm (Λ * U * Λ) ≤ s := by
    have hU0 := opNorm_nonneg' U
    have hL0 := opNorm_nonneg' Λ
    calc opNorm (Λ * U * Λ) ≤ opNorm Λ * opNorm U * opNorm Λ :=
          (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) hL0)
      _ ≤ 1 * s * 1 := by gcongr
      _ = s := by ring
  have key : ∀ n : ℕ, 2 ≤ n →
      |traceError K s (Λ * U * Λ) - traceError K s U| ≤
        2 * (d * (64 * s / n)) + 2 * T * (s * (16 / n + 16 / K)) := by
    intro n hn
    have hnr : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    set p := qScaled n s - qScaled K s with hp
    have h1 := split_err K n hn hs hVH hVs
    have h2 := split_err K n hn hs hU hUs
    have hB : ∀ x ∈ Set.Icc (-s) s, |x * (Polynomial.derivative p).eval x| ≤ s * (16 / n + 16 / K) := by
      intro x hx
      rw [hp, Polynomial.derivative_sub, Polynomial.eval_sub, qScaled_deriv n hs.ne',
        qScaled_deriv K hs.ne']
      have hy1 : -1 ≤ x / s := by rw [le_div_iff₀ hs]; linarith [hx.1]
      have hy2 : x / s ≤ 1 := by rw [div_le_iff₀ hs]; linarith [hx.2]
      have a1 := OTDJackson.q_sharp n hn hy1 hy2
      have a2 := OTDJackson.q_sharp K hK hy1 hy2
      have ex : x * ((q n).derivative.eval (x / s) - (q K).derivative.eval (x / s)) =
          s * (x / s * ((q n).derivative.eval (x / s) - (q K).derivative.eval (x / s))) := by
        field_simp
      rw [ex, abs_mul, abs_of_pos hs]
      refine mul_le_mul_of_nonneg_left ?_ hs.le
      calc |x / s * ((q n).derivative.eval (x / s) - (q K).derivative.eval (x / s))|
          = |(x / s) * (sign (x / s) - (q K).derivative.eval (x / s)) -
              (x / s) * (sign (x / s) - (q n).derivative.eval (x / s))| := by ring_nf
        _ ≤ |x / s| * |sign (x / s) - (q K).derivative.eval (x / s)| +
              |x / s| * |sign (x / s) - (q n).derivative.eval (x / s)| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
        _ ≤ 16 / n + 16 / K := by linarith
    have hB0 : 0 ≤ s * (16 / n + 16 / K) := by positivity
    have h3 := poly_congr p hU hUs hΛ hΛ1 hB0 hB
    have e := abs_sub_le (traceError K s (Λ * U * Λ) - (Polynomial.aeval (Λ * U * Λ) p).trace.re)
      0 0
    calc |traceError K s (Λ * U * Λ) - traceError K s U|
        = |(traceError K s (Λ * U * Λ) - (Polynomial.aeval (Λ * U * Λ) p).trace.re) -
            (traceError K s U - (Polynomial.aeval U p).trace.re) +
            ((Polynomial.aeval (Λ * U * Λ) p).trace.re - (Polynomial.aeval U p).trace.re)| := by
          ring_nf
      _ ≤ |traceError K s (Λ * U * Λ) - (Polynomial.aeval (Λ * U * Λ) p).trace.re| +
            |traceError K s U - (Polynomial.aeval U p).trace.re| +
            |(Polynomial.aeval (Λ * U * Λ) p).trace.re - (Polynomial.aeval U p).trace.re| := by
          refine (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
      _ ≤ d * (64 * s / n) + d * (64 * s / n) + 2 * T * (s * (16 / n + 16 / K)) := by
          gcongr
      _ = 2 * (d * (64 * s / n)) + 2 * T * (s * (16 / n + 16 / K)) := by ring
  refine le_of_forall_pos_le_add (fun δ hδ => ?_)
  set c := 128 * d * s + 32 * s * T with hc
  have hc0 : 0 ≤ c := by positivity
  set n : ℕ := ⌈c / δ⌉₊ + 2 with hn
  have hn2 : 2 ≤ n := by omega
  have hnr : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcn : c / n ≤ δ := by
    rw [div_le_iff₀ hnr]
    have h1 : c / δ ≤ n := by
      have := Nat.le_ceil (c / δ)
      have h2 : (⌈c / δ⌉₊ : ℝ) ≤ n := by rw [hn]; push_cast; linarith
      linarith
    rw [div_le_iff₀ hδ] at h1; linarith
  refine (key n hn2).trans ?_
  have e : 2 * (d * (64 * s / n)) + 2 * T * (s * (16 / n + 16 / K)) =
      c / n + (2:ℝ)^5 * s / K * T := by
    rw [hc]; field_simp; ring
  rw [e]; linarith

end final

end OTDA1

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
open OptimalTraceDistance.Estimation in
theorem solution (d K : ℕ) (hd : 0 < d) (hK : 2 ≤ K)
    (s : ℝ) (hs : 0 < s) (U Λ : Mat d) (hU : U.IsHermitian) (hUs : opNorm U ≤ s)
    (hΛ : Λ.PosDef) (hΛI : lePSD Λ 1) :
  |traceError K s (Λ * U * Λ) - traceError K s U| ≤
    (2 : ℝ)^5*s/K * QAlgorithms.traceNorm (logMat Λ) :=
  OTDA1.lemma_A_1_proof d K hd hK s hs U Λ hU hUs hΛ hΛI
