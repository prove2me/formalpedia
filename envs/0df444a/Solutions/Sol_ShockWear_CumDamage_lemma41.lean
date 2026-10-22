-- Prove2me | solution 1 for ShockWear.CumDamage.lemma41
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:09:33.97512+00:00
-- url     : https://prove2.me/submissions/55394970-49a7-427e-8234-eac53a5c4a90

import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model



namespace ShockWear.CumDamage

open MeasureTheory ProbabilityTheory

instance g23_convPow_prob (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (convPow μ k) := by
  induction k with
  | zero => simp only [convPow]; infer_instance
  | succ k ih => simp only [convPow]; infer_instance

lemma g23_convPow_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) (k : ℕ) :
    ∀ᵐ y ∂(convPow μ k), 0 ≤ y := by
  induction k with
  | zero => simp only [convPow]; simp
  | succ k ih =>
    simp only [convPow]
    have hμ' : ∀ᵐ y ∂μ, 0 ≤ y := by
      rw [ae_iff]
      have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
      rw [this]; exact hμ
    unfold Measure.conv
    refine (ae_map_iff (p := fun y : ℝ => 0 ≤ y) (by fun_prop) (measurableSet_Ici (a := (0:ℝ)))).2 ?_
    have h1 : ∀ᵐ p ∂((convPow μ k).prod μ), 0 ≤ p.1 := Measure.quasiMeasurePreserving_fst.ae ih
    have h2 : ∀ᵐ p ∂((convPow μ k).prod μ), 0 ≤ p.2 := Measure.quasiMeasurePreserving_snd.ae hμ'
    filter_upwards [h1, h2] with p h1 h2 using add_nonneg h1 h2

lemma g23_ae_nonneg (μ : Measure ℝ) (hμ : μ (Set.Iio 0) = 0) : ∀ᵐ y ∂μ, 0 ≤ y := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
  rw [this]; exact hμ

lemma g23_cdf_nonneg (μ : Measure ℝ) (k : ℕ) (x : ℝ) : 0 ≤ cdfPow μ k x := ENNReal.toReal_nonneg

lemma g23_cdf_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) (x : ℝ) :
    cdfPow μ k x ≤ 1 := by
  unfold cdfPow
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma g23_cdf_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) : Monotone (cdfPow μ k) := by
  intro a b hab
  unfold cdfPow
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.2 hab))

lemma g23_cdf_neg (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) (k : ℕ)
    (c : ℝ) (hc : c < 0) : cdfPow μ k c = 0 := by
  unfold cdfPow
  have h := g23_convPow_nonneg μ hμ k
  rw [ae_iff] at h
  have : convPow μ k (Set.Iic c) = 0 := by
    refine measure_mono_null (fun y hy => ?_) h
    simp only [Set.mem_Iic] at hy
    simp only [Set.mem_setOf_eq, not_le]; linarith
  rw [this]; rfl

lemma g23_cdf_zero (μ : Measure ℝ) (c : ℝ) (hc : 0 ≤ c) : cdfPow μ 0 c = 1 := by
  unfold cdfPow
  simp [convPow, hc]

lemma g23_conv_Iic (κ ν : Measure ℝ) [SFinite κ] [SFinite ν] (x : ℝ) :
    (κ.conv ν) (Set.Iic x) = ∫⁻ t, κ (Set.Iic (x - t)) ∂ν := by
  have hm : MeasurableSet ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iic x) :=
    (measurable_fst.add measurable_snd) measurableSet_Iic
  rw [Measure.conv, Measure.map_apply (f := fun p : ℝ × ℝ => p.1 + p.2) (by fun_prop) measurableSet_Iic,
    Measure.prod_apply_symm hm]
  congr 1
  ext t
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_Iic]
  constructor <;> intro h <;> linarith

lemma g23_cdf_succ (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℕ) (x : ℝ) :
    cdfPow μ (m + 1) x = ∫ t, cdfPow μ m (x - t) ∂μ := by
  unfold cdfPow
  simp only [convPow]
  rw [g23_conv_Iic]
  have hmeas : Measurable (fun t => convPow μ m (Set.Iic (x - t))) := by
    apply Antitone.measurable
    intro a b hab
    exact measure_mono (Set.Iic_subset_Iic.2 (by linarith))
  rw [integral_toReal hmeas.aemeasurable (Filter.Eventually.of_forall fun t => measure_lt_top _ _)]

lemma g23_cdf_meas (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℕ) (x : ℝ) :
    Measurable (fun t => cdfPow μ m (x - t)) := by
  apply Antitone.measurable
  intro a b hab
  exact g23_cdf_mono μ m (by linarith)

lemma g23_cdf_int (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℕ) (x : ℝ) :
    Integrable (fun t => cdfPow μ m (x - t)) μ :=
  Integrable.of_bound (g23_cdf_meas μ m x).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (g23_cdf_nonneg μ m _)]; exact g23_cdf_le_one μ m _)

/-- Q(m): a(m+1)^m ≤ a(m)^(m+1), and the pointwise step. -/
lemma g23_main (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    ∀ n : ℕ, ∀ c, cdfPow μ (n + 2) c ^ (n + 1) ≤ cdfPow μ (n + 1) c ^ (n + 2) := by
  set a := cdfPow μ with ha
  have hnn := g23_cdf_nonneg μ
  -- step: given pointwise bound for m ≥ 1, get Q(m)
  have step : ∀ m : ℕ, 1 ≤ m →
      (∀ x y, y ≤ x → a m y ≤ (a m x) ^ (1 / (m : ℝ)) * a (m - 1) y) →
      ∀ x, a (m + 1) x ^ m ≤ a m x ^ (m + 1) := by
    intro m hm hpt x
    have h1 : a (m + 1) x ≤ (a m x) ^ (1 / (m : ℝ)) * a m x := by
      have e3 : a m x = ∫ t, a (m - 1) (x - t) ∂μ := by
        have := g23_cdf_succ μ (m - 1) x
        rwa [Nat.sub_add_cancel hm] at this
      calc a (m + 1) x = ∫ t, a m (x - t) ∂μ := g23_cdf_succ μ m x
        _ ≤ ∫ t, (a m x) ^ (1 / (m : ℝ)) * a (m - 1) (x - t) ∂μ := by
          apply integral_mono_ae (g23_cdf_int μ m x) ((g23_cdf_int μ (m - 1) x).const_mul _)
          filter_upwards [g23_ae_nonneg μ hμ] with t ht
          exact hpt x (x - t) (by linarith)
        _ = (a m x) ^ (1 / (m : ℝ)) * a m x := by rw [integral_const_mul, ← e3]
    have hx := hnn m x
    have h2 : ((a m x) ^ (1 / (m : ℝ))) ^ m = a m x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
      have : (1 / (m : ℝ)) * (m : ℝ) = 1 := by
        have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
        field_simp
      rw [this, Real.rpow_one]
    calc a (m + 1) x ^ m ≤ ((a m x) ^ (1 / (m : ℝ)) * a m x) ^ m :=
          pow_le_pow_left₀ (hnn _ _) h1 m
      _ = a m x ^ (m + 1) := by rw [mul_pow, h2, pow_succ, mul_comm]
  intro n
  induction n with
  | zero =>
    apply step 1 le_rfl
    intro x y hyx
    simp only [Nat.cast_one, div_one, Real.rpow_one, Nat.sub_self]
    rcases lt_or_ge y 0 with hy | hy
    · rw [ha, g23_cdf_neg μ hμ 1 y hy]; exact mul_nonneg (hnn _ _) (hnn _ _)
    · rw [ha, g23_cdf_zero μ y hy, mul_one]; exact g23_cdf_mono μ 1 hyx
  | succ n ih =>
    apply step (n + 2) (by omega)
    intro x y hyx
    have hQ := ih y
    simp only [show n + 2 - 1 = n + 1 by omega]
    set u := a (n + 2) y
    set v := a (n + 1) y
    set w := a (n + 2) x
    have hu : 0 ≤ u := hnn _ _
    have hv : 0 ≤ v := hnn _ _
    have huw : u ≤ w := g23_cdf_mono μ (n + 2) hyx
    have hN : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have e1 : u = u ^ (1 / ((n + 2 : ℕ) : ℝ)) * (u ^ (n + 1)) ^ (1 / ((n + 2 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast u (n + 1), ← Real.rpow_mul hu, ← Real.rpow_add' hu]
      · have : 1 / ((n + 2 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) * (1 / ((n + 2 : ℕ) : ℝ)) = 1 := by
          push_cast; field_simp; ring
        rw [this, Real.rpow_one]
      · push_cast; positivity
    have e2 : (v ^ (n + 2)) ^ (1 / ((n + 2 : ℕ) : ℝ)) = v := by
      rw [← Real.rpow_natCast v (n + 2), ← Real.rpow_mul hv]
      rw [show ((n + 2 : ℕ) : ℝ) * (1 / ((n + 2 : ℕ) : ℝ)) = 1 by field_simp, Real.rpow_one]
    rw [e1]
    apply mul_le_mul
    · exact Real.rpow_le_rpow hu huw (by positivity)
    · rw [← e2]; exact Real.rpow_le_rpow (pow_nonneg hu _) hQ (by positivity)
    · exact Real.rpow_nonneg (pow_nonneg hu _) _
    · exact Real.rpow_nonneg (le_trans hu huw) _

theorem lemma41_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    ∀ (x : ℝ) (j k : ℕ), 1 ≤ j → j ≤ k →
      cdfPow μ k x ^ (1 / (k : ℝ)) ≤ cdfPow μ j x ^ (1 / (j : ℝ)) := by
  intro x j k hj hjk
  have hstep : ∀ m : ℕ, 1 ≤ m →
      cdfPow μ (m + 1) x ^ (1 / ((m + 1 : ℕ) : ℝ)) ≤ cdfPow μ m x ^ (1 / (m : ℝ)) := by
    intro m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hQ := g23_main μ hμ n x
    set u := cdfPow μ (n + 2) x
    set v := cdfPow μ (n + 1) x
    have hu : 0 ≤ u := g23_cdf_nonneg μ _ _
    have hv : 0 ≤ v := g23_cdf_nonneg μ _ _
    have hr : (0 : ℝ) ≤ 1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by positivity
    have h := Real.rpow_le_rpow (by positivity) hQ hr
    rw [← Real.rpow_natCast u, ← Real.rpow_natCast v, ← Real.rpow_mul hu,
      ← Real.rpow_mul hv] at h
    have e1 : ((n + 1 : ℕ) : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) =
        1 / ((n + 2 : ℕ) : ℝ) := by
      push_cast; field_simp
    have e2 : ((n + 2 : ℕ) : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) =
        1 / ((n + 1 : ℕ) : ℝ) := by
      push_cast; field_simp
    rw [e1, e2] at h
    have e4 : ((n + 1 + 1 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := rfl
    rw [e4]; exact h
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact le_trans (hstep k (le_trans hj hk)) ih

end ShockWear.CumDamage

open ShockWear.CumDamage
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    ∀ (x : ℝ) (j k : ℕ), 1 ≤ j → j ≤ k →
      cdfPow μ k x ^ (1 / (k : ℝ)) ≤ cdfPow μ j x ^ (1 / (j : ℝ)) := by
  exact lemma41_core μ hμ
