-- Prove2me | solution 1 for ShockWear.CumDamage.corollary42
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:12:57.837807+00:00
-- url     : https://prove2.me/submissions/01646f3f-a36f-4dc7-9ffe-164d6d563ff0

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

lemma g23_pw_nonneg (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) (k : ℕ) : 0 ≤ poisW lam t k := by
  unfold poisW
  have : 0 ≤ lam * t := mul_nonneg hlam ht
  positivity

lemma g23_pw_summable (lam t : ℝ) : Summable (fun k => poisW lam t k) := by
  unfold poisW
  have := (Real.summable_pow_div_factorial (lam * t)).mul_left (Real.exp (-(lam * t)))
  refine this.congr (fun k => ?_)
  ring

lemma g23_hasSum_geom (lam t ζ : ℝ) :
    HasSum (fun k => ζ ^ k * poisW lam t k) (Real.exp (-((1 - ζ) * lam * t))) := by
  have := (NormedSpace.expSeries_div_hasSum_exp (ζ * (lam * t))).mul_left (Real.exp (-(lam * t)))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add] at this
  have e1 : (fun k => ζ ^ k * poisW lam t k) =
      fun i => Real.exp (-(lam * t)) * ((ζ * (lam * t)) ^ i / (i.factorial : ℝ)) := by
    ext k; unfold poisW; rw [mul_pow]; ring
  have e2 : Real.exp (-((1 - ζ) * lam * t)) = Real.exp (-(lam * t) + ζ * (lam * t)) := by
    congr 1; ring
  rw [e1, e2]; exact this

lemma g23_bdd_summable (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) (a : ℕ → ℝ)
    (ha : ∀ k, |a k| ≤ 1) : Summable (fun k => a k * poisW lam t k) := by
  refine Summable.of_norm_bounded (g23_pw_summable lam t) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (g23_pw_nonneg lam t hlam ht k)]
  exact mul_le_of_le_one_left (g23_pw_nonneg lam t hlam ht k) (ha k)

lemma g23_P_bounds (P : ℕ → ℝ) (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (k : ℕ) : 0 ≤ P k ∧ P k ≤ 1 := ⟨hnn k, le_trans (hanti (Nat.zero_le k)) hP0⟩

lemma g23_transfer_eq (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 ≤ 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k) (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    shockSurv lam P t - Real.exp (-((1 - ζ) * lam * t)) =
        ∑' k, (P k - ζ ^ k) * poisW lam t k := by
  have hb := g23_P_bounds P hP0 hanti hnn
  have hs1 : Summable (fun k => P k * poisW lam t k) :=
    g23_bdd_summable lam t hlam.le ht P (fun k => by rw [abs_of_nonneg (hb k).1]; exact (hb k).2)
  have hs2 := (g23_hasSum_geom lam t ζ)
  unfold shockSurv
  rw [if_neg (not_lt.2 ht), ← hs2.tsum_eq, ← hs1.tsum_sub hs2.summable]
  congr 1; ext k; ring

/-- variation diminishing for the Poisson kernel -/
lemma g23_vd (lam : ℝ) (hlam : 0 < lam) (a : ℕ → ℝ) (ha : ∀ k, |a k| ≤ 1)
    (hsign : SignPMSeq a) (s t : ℝ) (hs : 0 ≤ s) (hst : s < t)
    (hgs : ∑' k, a k * poisW lam s k < 0) : ∑' k, a k * poisW lam t k ≤ 0 := by
  have ht : 0 ≤ t := by linarith
  have hex : ∃ N, a N < 0 := by
    by_contra h
    push_neg at h
    have : 0 ≤ ∑' k, a k * poisW lam s k :=
      tsum_nonneg (fun k => mul_nonneg (h k) (g23_pw_nonneg lam s hlam.le hs k))
    linarith
  classical
  let N := Nat.find hex
  have hN : a N < 0 := Nat.find_spec hex
  have hlow : ∀ k, k < N → 0 ≤ a k := fun k hk => by
    have := Nat.find_min hex hk; push_neg at this; exact this
  have hhigh : ∀ k, N ≤ k → a k ≤ 0 := fun k hk => by
    rcases hk.lt_or_eq with hk | hk
    · by_contra h; push_neg at h; exact hsign N k hk ⟨hN, h⟩
    · rw [← hk]; exact hN.le
  by_cases hN0 : N = 0
  · apply tsum_nonpos; intro k
    exact mul_nonpos_of_nonpos_of_nonneg (hhigh k (by omega)) (g23_pw_nonneg lam t hlam.le ht k)
  rcases hs.lt_or_eq with hs' | hs'
  · -- s > 0
    set r := t / s with hr
    have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hs']; linarith
    set C := Real.exp (-(lam * (t - s))) * r ^ N with hC
    have hCpos : 0 < C := by positivity
    have hpw : ∀ k, poisW lam t k = Real.exp (-(lam * (t - s))) * r ^ k * poisW lam s k := by
      intro k
      unfold poisW
      have e1 : lam * t = r * (lam * s) := by rw [hr]; field_simp
      have e2 : Real.exp (-(lam * t)) = Real.exp (-(lam * (t - s))) * Real.exp (-(lam * s)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e2]
      conv_lhs => rw [e1, mul_pow]
      ring
    have hterm : ∀ k, a k * poisW lam t k ≤ C * (a k * poisW lam s k) := by
      intro k
      rw [hpw k, hC]
      have hE := Real.exp_pos (-(lam * (t - s)))
      have hw := g23_pw_nonneg lam s hlam.le hs k
      rcases lt_or_ge k N with hk | hk
      · have h1 : r ^ k ≤ r ^ N := pow_le_pow_right₀ hr1 hk.le
        have h2 : 0 ≤ a k * poisW lam s k := mul_nonneg (hlow k hk) hw
        have : a k * (Real.exp (-(lam * (t - s))) * r ^ k * poisW lam s k) =
            Real.exp (-(lam * (t - s))) * (r ^ k * (a k * poisW lam s k)) := by ring
        rw [this, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h2) hE.le
      · have h1 : r ^ N ≤ r ^ k := pow_le_pow_right₀ hr1 hk
        have h2 : a k * poisW lam s k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hhigh k hk) hw
        have : a k * (Real.exp (-(lam * (t - s))) * r ^ k * poisW lam s k) =
            Real.exp (-(lam * (t - s))) * (r ^ k * (a k * poisW lam s k)) := by ring
        rw [this, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonpos_right h1 h2) hE.le
    have hS1 := g23_bdd_summable lam t hlam.le ht a ha
    have hS2 := (g23_bdd_summable lam s hlam.le hs a ha).mul_left C
    calc ∑' k, a k * poisW lam t k ≤ ∑' k, C * (a k * poisW lam s k) :=
          hS1.tsum_le_tsum hterm hS2
      _ = C * ∑' k, a k * poisW lam s k := tsum_mul_left
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hCpos.le hgs.le
  · -- s = 0
    exfalso
    subst hs'
    have : 0 ≤ ∑' k, a k * poisW lam 0 k := by
      apply tsum_nonneg
      intro k
      rcases lt_or_ge k N with hk | hk
      · exact mul_nonneg (hlow k hk) (g23_pw_nonneg lam 0 hlam.le le_rfl k)
      · have hk0 : k ≠ 0 := by omega
        simp [poisW, zero_pow hk0]
    linarith

theorem th31_core (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hroot : ∀ j k : ℕ, 1 ≤ j → j ≤ k → P k ^ (1 / (k : ℝ)) ≤ P j ^ (1 / (j : ℝ))) :
    IsIHRA (shockSurv lam P) := by
  have hP0' : P 0 ≤ 1 := hP0.le
  have hb := g23_P_bounds P hP0' hanti hnn
  -- sequence sign
  have hseq : ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 → SignPMSeq (fun k => P k - ζ ^ k) := by
    intro ζ hζ0 hζ1 j k hjk ⟨hj, hk⟩
    simp only at hj hk
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp [hP0] at hj
      · exact h
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj1
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have e : ∀ n : ℕ, (0 : ℝ) < n → (ζ ^ n) ^ (1 / (n : ℝ)) = ζ := by
      intro n hn
      rw [← Real.rpow_natCast, ← Real.rpow_mul hζ0, mul_one_div_cancel hn.ne', Real.rpow_one]
    have h1 : P j ^ (1 / (j : ℝ)) < ζ := by
      rw [← e j hjR]
      exact Real.rpow_lt_rpow (hnn j) (by linarith) (by positivity)
    have h2 : ζ < P k ^ (1 / (k : ℝ)) := by
      rw [← e k hkR]
      exact Real.rpow_lt_rpow (by positivity) (by linarith) (by positivity)
    have := hroot j k hj1 hjk.le
    linarith
  have habs : ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 → ∀ k, |P k - ζ ^ k| ≤ 1 := by
    intro ζ hζ0 hζ1 k
    have h1 := pow_le_one₀ hζ0 hζ1 (n := k)
    have h2 := pow_nonneg hζ0 k
    rw [abs_le]; constructor <;> linarith [(hb k).1, (hb k).2]
  -- exponential sign
  have hexp : ∀ θ : ℝ, 0 < θ → ∀ s t, 0 ≤ s → s < t →
      ¬ (shockSurv lam P s - Real.exp (-(θ * s)) < 0 ∧ 0 < shockSurv lam P t - Real.exp (-(θ * t))) := by
    intro θ hθ s t hs hst ⟨h1, h2⟩
    have ht : 0 ≤ t := by linarith
    rcases le_or_gt θ lam with hθl | hθl
    · set ζ := 1 - θ / lam with hζ
      have hζ0 : 0 ≤ ζ := by rw [hζ, sub_nonneg, div_le_one hlam]; exact hθl
      have hζ1 : ζ ≤ 1 := by rw [hζ]; have := div_pos hθ hlam; linarith
      have hθe : ∀ u, (1 - ζ) * lam * u = θ * u := by
        intro u; rw [hζ]; field_simp; ring
      have e := g23_transfer_eq lam hlam P hP0' hanti hnn ζ hζ0 hζ1
      rw [← hθe, e s hs] at h1
      rw [← hθe, e t ht] at h2
      have := g23_vd lam hlam _ (habs ζ hζ0 hζ1) (hseq ζ hζ0 hζ1) s t hs hst h1
      linarith
    · have e := g23_transfer_eq lam hlam P hP0' hanti hnn 0 le_rfl zero_le_one s hs
      have hnn' : 0 ≤ ∑' k, (P k - (0:ℝ) ^ k) * poisW lam s k := by
        apply tsum_nonneg; intro k
        apply mul_nonneg _ (g23_pw_nonneg lam s hlam.le hs k)
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp [hP0]
        · rw [zero_pow hk.ne']; simp [hnn k]
      have : Real.exp (-(θ * s)) ≤ Real.exp (-((1 - 0) * lam * s)) := by
        apply Real.exp_le_exp.2
        have : lam * s ≤ θ * s := mul_le_mul_of_nonneg_right hθl.le hs
        linarith
      linarith
  -- bounds on shockSurv
  have hH : ∀ t, 0 ≤ t → 0 ≤ shockSurv lam P t ∧ shockSurv lam P t ≤ 1 := by
    intro t ht
    constructor
    · unfold shockSurv; rw [if_neg (not_lt.2 ht)]
      exact tsum_nonneg (fun k => mul_nonneg (hnn k) (g23_pw_nonneg lam t hlam.le ht k))
    · have e := g23_transfer_eq lam hlam P hP0' hanti hnn 1 zero_le_one le_rfl t ht
      have : ∑' k, (P k - (1:ℝ) ^ k) * poisW lam t k ≤ 0 := by
        apply tsum_nonpos; intro k
        apply mul_nonpos_of_nonpos_of_nonneg _ (g23_pw_nonneg lam t hlam.le ht k)
        rw [one_pow]; linarith [(hb k).2]
      simp only [sub_self, zero_mul, neg_zero, Real.exp_zero] at e
      linarith
  -- IHRA
  intro s hs t ht hst
  simp only [Set.mem_Ioi] at hs ht
  by_contra hlt
  push_neg at hlt
  rcases hst.lt_or_eq with hst' | hst'
  swap
  · subst hst'; exact lt_irrefl _ hlt
  set H := shockSurv lam P
  set fs := H s ^ (1 / s)
  set ft := H t ^ (1 / t)
  have hfs0 : 0 ≤ fs := Real.rpow_nonneg (hH s hs.le).1 _
  have hft1 : ft ≤ 1 := Real.rpow_le_one (hH t ht.le).1 (hH t ht.le).2 (by positivity)
  set c := (fs + ft) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hc1 : c < 1 := by rw [hc]; linarith
  have hcs : fs < c := by rw [hc]; linarith
  have hct : c < ft := by rw [hc]; linarith
  set θ := -Real.log c with hθ
  have hθpos : 0 < θ := by rw [hθ]; have := Real.log_neg hc0 hc1; linarith
  have hexpc : ∀ u, Real.exp (-(θ * u)) = c ^ u := by
    intro u; rw [Real.rpow_def_of_pos hc0, hθ]; congr 1; ring
  have hroot_pow : ∀ u, 0 < u → (H u ^ (1 / u)) ^ u = H u := by
    intro u hu
    rw [← Real.rpow_mul (hH u hu.le).1, one_div_mul_cancel hu.ne', Real.rpow_one]
  have h1 : H s < c ^ s := by
    rw [← hroot_pow s hs]
    exact Real.rpow_lt_rpow hfs0 hcs hs
  have h2 : c ^ t < H t := by
    rw [← hroot_pow t ht]
    exact Real.rpow_lt_rpow hc0.le hct ht
  apply hexp θ hθpos s t hs.le hst'
  rw [hexpc, hexpc]
  constructor <;> linarith

lemma g23_cdf_anti (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) (x : ℝ) :
    Antitone (fun k => cdfPow μ k x) := by
  apply antitone_nat_of_succ_le
  intro k
  show cdfPow μ (k + 1) x ≤ cdfPow μ k x
  rw [g23_cdf_succ]
  calc ∫ t, cdfPow μ k (x - t) ∂μ ≤ ∫ _t, cdfPow μ k x ∂μ := by
        apply integral_mono_ae (g23_cdf_int μ k x) (integrable_const _)
        filter_upwards [g23_ae_nonneg μ hμ] with t ht
        exact g23_cdf_mono μ k (by linarith)
    _ = cdfPow μ k x := by simp

theorem cor42_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    IsIHRA (shockSurv lam (fun k => cdfPow μ k x)) := by
  rcases lt_or_ge x 0 with hx | hx
  · intro s hs t ht _
    simp only [Set.mem_Ioi] at hs ht
    have h0 : ∀ u, 0 < u → shockSurv lam (fun k => cdfPow μ k x) u = 0 := by
      intro u hu
      unfold shockSurv
      rw [if_neg (not_lt.2 hu.le)]
      simp [g23_cdf_neg μ hμ _ x hx]
    simp only
    rw [h0 s hs, h0 t ht, Real.zero_rpow (by positivity), Real.zero_rpow (by positivity)]
  · exact th31_core lam hlam _ (g23_cdf_zero μ x hx) (g23_cdf_anti μ hμ x)
      (fun k => g23_cdf_nonneg μ k x) (fun j k hj hjk => lemma41_core μ hμ x j k hj hjk)

end ShockWear.CumDamage

open ShockWear.CumDamage
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    IsIHRA (shockSurv lam (fun k => cdfPow μ k x)) := by
  exact cor42_core μ hμ lam hlam x
