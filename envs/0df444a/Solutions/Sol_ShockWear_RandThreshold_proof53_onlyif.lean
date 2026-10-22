-- Prove2me | solution 1 for ShockWear.RandThreshold.proof53_onlyif
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:22:55.36756+00:00
-- url     : https://prove2.me/submissions/61753dd6-6054-4d56-948b-d4935ba8d1f7

import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model



namespace ShockWear.RandThreshold

open MeasureTheory ProbabilityTheory

/-! ### Theorem 31.5 core -/

lemma poisW_nonneg (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t) (k : ℕ) : 0 ≤ poisW lam t k := by
  unfold poisW
  have : 0 ≤ lam * t := mul_nonneg hlam ht
  positivity

lemma poisW_summable (lam t : ℝ) : Summable (fun k => poisW lam t k) := by
  unfold poisW
  have := (Real.summable_pow_div_factorial (lam * t)).mul_left (Real.exp (-(lam * t)))
  refine this.congr (fun k => ?_)
  ring

lemma poisW_add (lam t x : ℝ) (n : ℕ) :
    poisW lam (t + x) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, poisW lam t p.1 * poisW lam x p.2 := by
  unfold poisW
  have h1 : (lam * (t + x)) = lam * t + lam * x := by ring
  rw [h1, (Commute.all (lam * t) (lam * x)).add_pow', Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  obtain ⟨i, j⟩ := p
  simp only at hp ⊢
  subst hp
  have hc : ((i + j).choose i : ℝ) * (i.factorial : ℝ) * (j.factorial : ℝ) = ((i + j).factorial : ℝ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial i j
    rw [Nat.choose_symm_add]
    exact_mod_cast this
  have hi : (i.factorial : ℝ) ≠ 0 := by positivity
  have hj : (j.factorial : ℝ) ≠ 0 := by positivity
  have hij : ((i + j).factorial : ℝ) ≠ 0 := by positivity
  rw [neg_add, Real.exp_add]
  rw [nsmul_eq_mul]
  rw [← hc]
  have hch : ((i + j).choose i : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right i j)).ne'
  field_simp

theorem t315_core (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hsub : ∀ j k, P (j + k) ≤ P j * P k) :
    IsNBU (shockSurv lam P) := by
  intro x t hx ht
  have hP1 : ∀ k, P k ≤ 1 := fun k => by
    have := hanti (Nat.zero_le k); rwa [hP0] at this
  unfold shockSurv
  simp only [not_lt.mpr hx, not_lt.mpr ht, not_lt.mpr (add_nonneg ht hx), if_false]
  set a := fun k => poisW lam t k with ha
  set b := fun k => poisW lam x k with hb
  have ha0 : ∀ k, 0 ≤ a k := fun k => poisW_nonneg lam t hlam.le ht k
  have hb0 : ∀ k, 0 ≤ b k := fun k => poisW_nonneg lam x hlam.le hx k
  have hsa : Summable (fun k => P k * a k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hnn k) (ha0 k))
      (fun k => by simpa using mul_le_mul_of_nonneg_right (hP1 k) (ha0 k)) (poisW_summable lam t)
  have hsb : Summable (fun k => P k * b k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hnn k) (hb0 k))
      (fun k => by simpa using mul_le_mul_of_nonneg_right (hP1 k) (hb0 k)) (poisW_summable lam x)
  have hna : Summable (fun k => ‖P k * a k‖) := by
    refine hsa.congr (fun k => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hnn k) (ha0 k))]
  have hnb : Summable (fun k => ‖P k * b k‖) := by
    refine hsb.congr (fun k => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hnn k) (hb0 k))]
  rw [mul_comm, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]
  have hsR := summable_norm_sum_mul_antidiagonal_of_summable_norm hna hnb
  have hle : ∀ n, P n * poisW lam (t + x) n ≤
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (P kl.1 * a kl.1) * (P kl.2 * b kl.2) := by
    intro n
    rw [poisW_add, Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h := hsub p.1 p.2
    rw [hp] at h
    have : 0 ≤ a p.1 * b p.2 := mul_nonneg (ha0 _) (hb0 _)
    calc P n * (poisW lam t p.1 * poisW lam x p.2) = P n * (a p.1 * b p.2) := rfl
      _ ≤ (P p.1 * P p.2) * (a p.1 * b p.2) := mul_le_mul_of_nonneg_right h this
      _ = _ := by ring
  have hnnL : ∀ n, 0 ≤ P n * poisW lam (t + x) n := fun n =>
    mul_nonneg (hnn n) (poisW_nonneg lam (t + x) hlam.le (add_nonneg ht hx) n)
  have hsR' : Summable (fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (P kl.1 * a kl.1) * (P kl.2 * b kl.2)) :=
    hsR.of_norm
  have hsL := Summable.of_nonneg_of_le hnnL hle hsR'
  exact hsL.tsum_le_tsum hle hsR'


/-! ### measure-theoretic lemmas -/

/-- closed survival `ν [y, ∞)` -/
noncomputable def Gs (ν : Measure ℝ) (y : ℝ) : ℝ := ν.real (Set.Ici y)

lemma Gs_nonneg (ν : Measure ℝ) (y : ℝ) : 0 ≤ Gs ν y := measureReal_nonneg

lemma Gs_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (y : ℝ) : Gs ν y ≤ 1 := by
  unfold Gs; exact measureReal_le_one

lemma Gs_anti (ν : Measure ℝ) [IsProbabilityMeasure ν] : Antitone (Gs ν) := by
  intro a b hab
  unfold Gs
  exact measureReal_mono (Set.Ici_subset_Ici.mpr hab)

lemma Gs_meas (ν : Measure ℝ) [IsProbabilityMeasure ν] : Measurable (Gs ν) :=
  (Gs_anti ν).measurable

lemma survOf_nonneg (ν : Measure ℝ) (y : ℝ) : 0 ≤ survOf ν y := ENNReal.toReal_nonneg

lemma survOf_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (y : ℝ) : survOf ν y ≤ 1 := by
  unfold survOf
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma survOf_anti (ν : Measure ℝ) [IsProbabilityMeasure ν] : Antitone (survOf ν) := by
  intro a b hab
  unfold survOf
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi hab))

lemma survOf_le_Gs (ν : Measure ℝ) [IsProbabilityMeasure ν] (a : ℝ) : survOf ν a ≤ Gs ν a := by
  unfold survOf Gs
  rw [Measure.real]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.Ioi_subset_Ici_self)

lemma Gs_le_survOf (ν : Measure ℝ) [IsProbabilityMeasure ν] {a b : ℝ} (hab : a < b) :
    Gs ν b ≤ survOf ν a := by
  unfold survOf Gs
  rw [Measure.real]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun x hx => lt_of_lt_of_le hab hx))

lemma Gs_zero (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0) : Gs ν 0 = 1 := by
  unfold Gs
  rw [Measure.real]
  have : ν (Set.Ici 0) = 1 := by
    have h := prob_compl_eq_one_sub (μ := ν) (measurableSet_Iio (a := (0:ℝ)))
    rw [hν, Set.compl_Iio] at h
    simpa using h
  rw [this]; simp

lemma tendsto_survOf_right (ν : Measure ℝ) [IsProbabilityMeasure ν] (a c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ => survOf ν (a + c / (n + 1))) Filter.atTop (nhds (survOf ν a)) := by
  have hmono : Monotone (fun n : ℕ => Set.Ioi (a + c / (n + 1))) := by
    intro m n hmn
    apply Set.Ioi_subset_Ioi
    have : c / ((n:ℝ) + 1) ≤ c / ((m:ℝ) + 1) := by
      apply div_le_div_of_nonneg_left hc.le (by positivity)
      have : (m:ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    linarith
  have h := tendsto_measure_iUnion_atTop (μ := ν) hmono
  have hU : (⋃ n : ℕ, Set.Ioi (a + c / (n + 1))) = Set.Ioi a := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < c / ((n:ℝ) + 1) := by positivity
      linarith
    · intro hx
      have hpos : 0 < x - a := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (c / (x - a))
      refine ⟨n, ?_⟩
      have : c / ((n:ℝ) + 1) < x - a := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at hn
        nlinarith
      linarith
  rw [hU] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

lemma tendsto_Gs_left (ν : Measure ℝ) [IsProbabilityMeasure ν] (a : ℝ) :
    Filter.Tendsto (fun n : ℕ => survOf ν (a - 1 / (n + 1))) Filter.atTop (nhds (Gs ν a)) := by
  have hanti : Antitone (fun n : ℕ => Set.Ioi (a - 1 / ((n:ℝ) + 1))) := by
    intro m n hmn
    apply Set.Ioi_subset_Ioi
    have : 1 / ((n:ℝ) + 1) ≤ 1 / ((m:ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m:ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    linarith
  have h := tendsto_measure_iInter_atTop (μ := ν) (fun n => measurableSet_Ioi.nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hU : (⋂ n : ℕ, Set.Ioi (a - 1 / ((n:ℝ) + 1))) = Set.Ici a := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_Ici]
    constructor
    · intro hx
      by_contra hlt
      rw [not_le] at hlt
      have hpos : 0 < a - x := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (a - x))
      have := hx n
      have : 1 / ((n:ℝ) + 1) < a - x := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at hn
        nlinarith
      linarith [hx n]
    · intro hx n
      have : 0 < 1 / ((n:ℝ) + 1) := by positivity
      linarith
  rw [hU] at h
  have := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  exact this

lemma Gs_nbu (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hG : IsNBU (survOf ν)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Gs ν (a + b) ≤ Gs ν a * Gs ν b := by
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add, Gs_zero ν hν, one_mul]
  rcases hb.eq_or_lt with rfl | hb'
  · rw [add_zero, Gs_zero ν hν, mul_one]
  have h1 := tendsto_Gs_left ν a
  have h2 := tendsto_Gs_left ν b
  have hm : 0 < min a b := lt_min ha' hb'
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / min a b)
  refine le_of_tendsto_of_tendsto tendsto_const_nhds (h1.mul h2)
    (Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  have hlt : 1 / ((n:ℝ) + 1) < min a b := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hm] at hN
    have : (N:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hle1 : 1 / ((n:ℝ) + 1) < a := lt_of_lt_of_le hlt (min_le_left _ _)
  have hle2 : 1 / ((n:ℝ) + 1) < b := lt_of_lt_of_le hlt (min_le_right _ _)
  have hpos : 0 < 1 / ((n:ℝ) + 1) := by positivity
  show Gs ν (a + b) ≤ survOf ν (a - 1 / (n + 1)) * survOf ν (b - 1 / (n + 1))
  calc Gs ν (a + b) ≤ survOf ν (a + b - 1 / ((n:ℝ) + 1)) := Gs_le_survOf ν (by linarith)
    _ ≤ survOf ν ((b - 1 / ((n:ℝ) + 1)) + (a - 1 / ((n:ℝ) + 1))) :=
        survOf_anti ν (by linarith)
    _ ≤ survOf ν (a - 1 / ((n:ℝ) + 1)) * survOf ν (b - 1 / ((n:ℝ) + 1)) :=
        hG _ _ (by linarith) (by linarith)


/-! ### convolution powers -/

instance convPow_prob (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (convPow μ k) := by
  induction k with
  | zero => simp only [convPow]; infer_instance
  | succ k ih => simp only [convPow]; infer_instance

lemma convPow_add (μ : Measure ℝ) [IsProbabilityMeasure μ] (j k : ℕ) :
    convPow μ (j + k) = Measure.conv (convPow μ j) (convPow μ k) := by
  induction k with
  | zero =>
    simp only [add_zero, convPow]
    exact (Measure.conv_dirac_zero _).symm
  | succ k ih =>
    rw [← add_assoc]
    simp only [convPow]
    rw [ih, Measure.conv_assoc]

lemma convPow_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) (k : ℕ) :
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

lemma randP_eq (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (k : ℕ) :
    randP μ ν k = ∫ y, Gs ν y ∂(convPow μ k) := by
  set κ := convPow μ k with hκ
  let f : ℝ × ℝ → ℝ := fun p => (Set.Iic p.2).indicator (fun _ => (1:ℝ)) p.1
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
  have hf : f = {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun _ => (1:ℝ)) := by
    ext p; simp [f, Set.indicator, Set.mem_Iic]
  have hfm : Measurable f := by rw [hf]; exact measurable_const.indicator hmeas
  have hint : Integrable f (κ.prod ν) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun p => ?_)
    rw [hf]; simp only [Set.indicator]; split_ifs <;> simp
  have h1 : ∀ x, cdfPow μ k x = ∫ y, f (y, x) ∂κ := by
    intro x
    simp only [f]
    rw [integral_indicator_const _ measurableSet_Iic]
    simp [cdfPow, Measure.real, hκ]
  have h2 : ∀ y, Gs ν y = ∫ x, f (y, x) ∂ν := by
    intro y
    have : (fun x => f (y, x)) = (Set.Ici y).indicator (fun _ => (1:ℝ)) := by
      ext x; simp [f, Set.indicator, Set.mem_Iic, Set.mem_Ici]
    rw [this, integral_indicator_const _ measurableSet_Ici]
    simp [Gs]
  unfold randP
  simp_rw [h1, h2]
  exact (integral_integral_swap hint).symm


lemma integrable_Gs (ν : Measure ℝ) [IsProbabilityMeasure ν] (κ : Measure ℝ) [IsProbabilityMeasure κ] :
    Integrable (Gs ν) κ :=
  Integrable.of_bound (Gs_meas ν).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (Gs_nonneg ν y)]; exact Gs_le_one ν y)

theorem if_core (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hG : IsNBU (survOf ν)) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) :
    ∀ j k : ℕ, randP μ ν (j + k) ≤ randP μ ν j * randP μ ν k := by
  intro j k
  rw [randP_eq, randP_eq, randP_eq, convPow_add]
  unfold Measure.conv
  rw [integral_map (by fun_prop) (Gs_meas ν).aestronglyMeasurable]
  rw [← integral_prod_mul (Gs ν) (Gs ν)]
  have hj := convPow_nonneg μ hμ j
  have hk := convPow_nonneg μ hμ k
  have h1 : ∀ᵐ p ∂((convPow μ j).prod (convPow μ k)), 0 ≤ p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hj
  have h2 : ∀ᵐ p ∂((convPow μ j).prod (convPow μ k)), 0 ≤ p.2 :=
    Measure.quasiMeasurePreserving_snd.ae hk
  have hi1 : Integrable (fun p : ℝ × ℝ => Gs ν (p.1 + p.2)) ((convPow μ j).prod (convPow μ k)) :=
    Integrable.of_bound ((Gs_meas ν).comp (by fun_prop)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Gs_nonneg ν _)]; exact Gs_le_one ν _)
  have hi2 : Integrable (fun p : ℝ × ℝ => Gs ν p.1 * Gs ν p.2) ((convPow μ j).prod (convPow μ k)) :=
    Integrable.of_bound (((Gs_meas ν).comp measurable_fst).mul ((Gs_meas ν).comp measurable_snd)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (mul_nonneg (Gs_nonneg ν _) (Gs_nonneg ν _))]
        calc Gs ν y.1 * Gs ν y.2 ≤ 1 * 1 :=
              mul_le_mul (Gs_le_one ν _) (Gs_le_one ν _) (Gs_nonneg ν _) zero_le_one
          _ = 1 := by norm_num)
  refine integral_mono_ae hi1 hi2 ?_
  filter_upwards [h1, h2] with p h1 h2
  exact Gs_nbu ν hν hG h1 h2


/-! ### only-if direction -/

lemma convPow_dirac (d : ℝ) (n : ℕ) : convPow (Measure.dirac d) n = Measure.dirac ((n:ℝ) * d) := by
  induction n with
  | zero => simp [convPow]
  | succ n ih =>
    simp only [convPow, ih]
    rw [Measure.dirac_conv_dirac]
    congr 1
    push_cast; ring

lemma grid_sub (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsub : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
      ∀ j k : ℕ, randP μ ν (j + k) ≤ randP μ ν j * randP μ ν k)
    {d : ℝ} (hd : 0 ≤ d) (j k : ℕ) :
    Gs ν (((j:ℝ) + k) * d) ≤ Gs ν ((j:ℝ) * d) * Gs ν ((k:ℝ) * d) := by
  haveI : IsProbabilityMeasure (Measure.dirac d) := inferInstance
  have h0 : (Measure.dirac d) (Set.Iio 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iio]
    simp [Set.indicator, not_lt.mpr hd]
  have := hsub (Measure.dirac d) inferInstance h0 j k
  simp only [randP_eq, convPow_dirac] at this
  rw [integral_dirac, integral_dirac, integral_dirac] at this
  push_cast at this
  exact this

lemma Gs_pow_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsub : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
      ∀ j k : ℕ, randP μ ν (j + k) ≤ randP μ ν j * randP μ ν k)
    {d : ℝ} (hd : 0 ≤ d) (n : ℕ) (hn : 1 ≤ n) :
    Gs ν ((n:ℝ) * d) ≤ Gs ν d ^ n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have := grid_sub ν hsub hd n 1
    simp only [Nat.cast_one, one_mul] at this
    calc Gs ν (((n+1:ℕ):ℝ) * d) ≤ Gs ν ((n:ℝ) * d) * Gs ν d := by push_cast; exact this
      _ ≤ Gs ν d ^ n * Gs ν d := mul_le_mul_of_nonneg_right ih (Gs_nonneg ν _)
      _ = Gs ν d ^ (n+1) := by ring

theorem onlyif_core (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hsub : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
      ∀ j k : ℕ, randP μ ν (j + k) ≤ randP μ ν j * randP μ ν k) :
    ∀ s : ℝ, 0 < s → ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ,
      survOf ν (s + j * (s / k)) ≤ survOf ν s * survOf ν (j * (s / k)) := by
  intro s hs k hk j
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- j = 0
    simp only [Nat.cast_zero, zero_mul, add_zero]
    by_cases hG0 : survOf ν 0 < 1
    · have hlim : Filter.Tendsto (fun n : ℕ => survOf ν 0 ^ n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (survOf_nonneg ν 0) hG0
      have hle : Gs ν s ≤ 0 := by
        refine ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
        have hnpos : (0:ℝ) < n := by exact_mod_cast hn
        have h1 := Gs_pow_le ν hsub (d := s / n) (by positivity) n hn
        have h2 : Gs ν (s / n) ≤ survOf ν 0 := Gs_le_survOf ν (by positivity)
        calc Gs ν s = Gs ν ((n:ℝ) * (s / n)) := by field_simp
          _ ≤ Gs ν (s / n) ^ n := h1
          _ ≤ survOf ν 0 ^ n := pow_le_pow_left₀ (Gs_nonneg ν _) h2 n
      have : survOf ν s ≤ 0 := (survOf_le_Gs ν s).trans hle
      have h0 : survOf ν s = 0 := le_antisymm this (survOf_nonneg ν s)
      rw [h0]; simp
    · have : 1 ≤ survOf ν 0 := not_lt.mp hG0
      have := survOf_nonneg ν s
      nlinarith
  · -- j ≥ 1
    have hu : 0 < (j:ℝ) * (s / k) := by
      have : (0:ℝ) < j := by exact_mod_cast hj
      positivity
    set u := (j:ℝ) * (s / k) with hu_def
    have hlim := tendsto_survOf_right ν (s + u) (s + u) (by linarith)
    refine le_of_tendsto' hlim (fun n => ?_)
    have hδ : 0 < 1 / ((n:ℝ) + 1) := by positivity
    set δ := 1 / ((n:ℝ) + 1) with hδdef
    set d := (1 + δ) * (s / k) with hd
    have hd0 : 0 ≤ d := by positivity
    have hg := grid_sub ν hsub hd0 j k
    have e1 : ((j:ℝ) + k) * d = (s + u) + (s + u) / ((n:ℝ) + 1) := by
      rw [hd, hu_def, hδdef]; field_simp; ring
    have e2 : (j:ℝ) * d = (1 + δ) * u := by rw [hd, hu_def]; ring
    have e3 : (k:ℝ) * d = (1 + δ) * s := by rw [hd]; field_simp
    rw [e1, e2, e3] at hg
    have hGu : Gs ν ((1 + δ) * u) ≤ survOf ν u :=
      Gs_le_survOf ν (by nlinarith)
    have hGs : Gs ν ((1 + δ) * s) ≤ survOf ν s :=
      Gs_le_survOf ν (by nlinarith)
    calc survOf ν (s + u + (s + u) / ((n:ℝ) + 1)) ≤ Gs ν ((s + u) + (s + u) / ((n:ℝ) + 1)) :=
          survOf_le_Gs ν _
      _ ≤ _ := hg
      _ ≤ survOf ν u * survOf ν s :=
          mul_le_mul hGu hGs (Gs_nonneg ν _) (survOf_nonneg ν _)
      _ = _ := mul_comm _ _

end ShockWear.RandThreshold

open ShockWear.RandThreshold
open MeasureTheory ProbabilityTheory

theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hsub : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
      ∀ j k : ℕ, randP μ ν (j + k) ≤ randP μ ν j * randP μ ν k) :
    ∀ s : ℝ, 0 < s → ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ,
      survOf ν (s + j * (s / k)) ≤ survOf ν s * survOf ν (j * (s / k)) := by
  exact onlyif_core ν hν hsub
