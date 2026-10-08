-- Prove2me | solution 1 for QueueingFundamentals.GM1.serviceProb_properties
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:19:16.803206+00:00
-- url     : https://prove2.me/submissions/9c13d8cf-e408-462f-91f2-cc1e3b13d971

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QGM1Helpers5372

open MeasureTheory

lemma pt_hasSum (m t : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-m * t) * (m * t) ^ n / (Nat.factorial n : ℝ)) 1 := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (m * t)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-m * t))
  have h3 : Real.exp (-m * t) * Real.exp (m * t) = 1 := by
    rw [← Real.exp_add]; simp
  rw [h3] at h2
  have e : (fun n : ℕ => Real.exp (-m * t) * (m * t) ^ n / (Nat.factorial n : ℝ)) =
      (fun i : ℕ => Real.exp (-m * t) * ((m * t) ^ i / (Nat.factorial i : ℝ))) := by
    funext n; ring
  rw [e]; exact h2

lemma pt_hasSum_mean (m t : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-m * t) * (m * t) ^ n / (Nat.factorial n : ℝ)))
      (m * t) := by
  rw [← hasSum_nat_add_iff' 1]
  have h := (pt_hasSum m t).mul_left (m * t)
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero, mul_one]
    at h ⊢
  refine h.congr_fun (fun n => ?_)
  rw [Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma pt_nonneg (m t : ℝ) (hm : 0 < m) (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ Real.exp (-m * t) * (m * t) ^ n / (Nat.factorial n : ℝ) := by
  have : 0 ≤ m * t := mul_nonneg hm.le ht
  positivity

lemma pt_pos (m t : ℝ) (hm : 0 < m) (ht : 0 < t) (n : ℕ) :
    0 < Real.exp (-m * t) * (m * t) ^ n / (Nat.factorial n : ℝ) := by
  have : 0 < m * t := mul_pos hm ht
  positivity

lemma pt_le_one (m t : ℝ) (hm : 0 < m) (ht : 0 ≤ t) (n : ℕ) :
    Real.exp (-m * t) * (m * t) ^ n / (Nat.factorial n : ℝ) ≤ 1 :=
  le_hasSum (pt_hasSum m t) n (fun j _ => pt_nonneg m t hm ht j)

lemma pt_mean_le (m t : ℝ) (hm : 0 < m) (ht : 0 ≤ t) (n : ℕ) :
    (n : ℝ) * (Real.exp (-m * t) * (m * t) ^ n / (Nat.factorial n : ℝ)) ≤ m * t :=
  le_hasSum (pt_hasSum_mean m t) n
    (fun j _ => mul_nonneg (Nat.cast_nonneg j) (pt_nonneg m t hm ht j))

lemma pt_cont (m : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => Real.exp (-m * t) * (m * t) ^ n / (Nat.factorial n : ℝ)) := by
  fun_prop

end QGM1Helpers5372

open QGM1Helpers5372 in
open QueueingFundamentals.GM1 MeasureTheory in
theorem solution (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) :
    0 < serviceProb A mu 0 ∧ serviceProb A mu 0 < 1 ∧
      (∀ n, 0 < serviceProb A mu n) ∧
      HasSum (fun n : ℕ => serviceProb A mu n) 1 ∧
      HasSum (fun n : ℕ => (n : ℝ) * serviceProb A mu n) (mu / lam) := by
  have := hA.isProbability
  have hae : ∀ᵐ x ∂A, x ∈ Set.Ici (0 : ℝ) := by
    rw [ae_iff]
    have : {a : ℝ | ¬ a ∈ Set.Ici (0 : ℝ)} = Set.Iio 0 := by
      ext a; simp
    rw [this]; exact hA.nonneg
  have hres : A.restrict (Set.Ici (0 : ℝ)) = A := Measure.restrict_eq_self_of_ae_mem hae
  have hsp : ∀ n, QueueingFundamentals.GM1.serviceProb A mu n =
      ∫ t, Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ) ∂A := by
    intro n
    unfold QueueingFundamentals.GM1.serviceProb
    rw [hres]
  have hint : ∀ n, Integrable
      (fun t : ℝ => Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ)) A := by
    intro n
    refine Integrable.mono' (integrable_const (1 : ℝ)) (pt_cont mu n).aestronglyMeasurable ?_
    filter_upwards [hae] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (pt_nonneg mu t hmu ht n)]
    exact pt_le_one mu t hmu ht n
  -- A(Ioi 0) > 0
  have hpos : 0 < A (Set.Ioi (0 : ℝ)) := by
    rw [pos_iff_ne_zero]
    intro h0
    have hz : ∀ᵐ x ∂A, x = 0 := by
      rw [ae_iff]
      have : {a : ℝ | ¬ a = 0} = Set.Iio 0 ∪ Set.Ioi 0 := by
        rw [Set.Iio_union_Ioi]; rfl
      rw [this]
      exact measure_union_null hA.nonneg h0
    have : ∫ x, x ∂A = 0 := by
      rw [integral_congr_ae hz]; simp
    rw [hA.mean] at this
    have : (0 : ℝ) < 1 / lam := by positivity
    linarith
  have hbpos : ∀ n, 0 < QueueingFundamentals.GM1.serviceProb A mu n := by
    intro n
    rw [hsp n, integral_pos_iff_support_of_nonneg_ae _ (hint n)]
    · refine lt_of_lt_of_le hpos (measure_mono ?_)
      intro t ht
      exact (pt_pos mu t hmu ht n).ne'
    · filter_upwards [hae] with t ht
      exact pt_nonneg mu t hmu ht n
  have hsum : HasSum (fun n : ℕ => QueueingFundamentals.GM1.serviceProb A mu n) 1 := by
    have h := hasSum_integral_of_dominated_convergence (μ := A)
      (F := fun n t => Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ))
      (f := fun _ => (1 : ℝ))
      (fun n t => Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ))
      (fun n => (pt_cont mu n).aestronglyMeasurable)
      (fun n => by
        filter_upwards [hae] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (pt_nonneg mu t hmu ht n)])
      (Filter.Eventually.of_forall fun t => (pt_hasSum mu t).summable)
      (by
        have : (fun t : ℝ => ∑' n : ℕ,
            Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ)) = fun _ => (1 : ℝ) := by
          funext t; exact (pt_hasSum mu t).tsum_eq
        rw [this]; exact integrable_const _)
      (Filter.Eventually.of_forall fun t => pt_hasSum mu t)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
    have e : (fun n : ℕ => serviceProb A mu n) =
        (fun n : ℕ => ∫ a, Real.exp (-mu * a) * (mu * a) ^ n / (Nat.factorial n : ℝ) ∂A) := by
      funext n; exact hsp n
    rw [e]; exact h
  have hmean : HasSum (fun n : ℕ => (n : ℝ) * QueueingFundamentals.GM1.serviceProb A mu n)
      (mu / lam) := by
    have hI : Integrable (fun t : ℝ => mu * t) A := hA.integrable.const_mul mu
    have h := hasSum_integral_of_dominated_convergence (μ := A)
      (F := fun (n : ℕ) t => (n : ℝ) * (Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ)))
      (f := fun t => mu * t)
      (fun (n : ℕ) t => (n : ℝ) * (Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ)))
      (fun n => (continuous_const.mul (pt_cont mu n)).aestronglyMeasurable)
      (fun n => by
        filter_upwards [hae] with t ht
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (pt_nonneg mu t hmu ht n))])
      (Filter.Eventually.of_forall fun t => (pt_hasSum_mean mu t).summable)
      (by
        have : (fun t : ℝ => ∑' n : ℕ, (n : ℝ) *
            (Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ))) = fun t => mu * t := by
          funext t; exact (pt_hasSum_mean mu t).tsum_eq
        rw [this]; exact hI)
      (Filter.Eventually.of_forall fun t => pt_hasSum_mean mu t)
    rw [integral_const_mul, hA.mean] at h
    have e : (fun n : ℕ => (n : ℝ) * serviceProb A mu n) =
        (fun n : ℕ => ∫ a, (n : ℝ) *
          (Real.exp (-mu * a) * (mu * a) ^ n / (Nat.factorial n : ℝ)) ∂A) := by
      funext n; rw [hsp n, ← integral_const_mul]
    have e2 : mu / lam = mu * (1 / lam) := by ring
    rw [e, e2]; exact h
  refine ⟨hbpos 0, ?_, hbpos, hsum, hmean⟩
  have h01 := sum_le_hasSum (Finset.range 2) (fun i _ => (hbpos i).le) hsum
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h01
  linarith [hbpos 1]
