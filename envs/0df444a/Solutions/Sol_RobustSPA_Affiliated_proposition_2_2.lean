-- Prove2me | solution 2 for RobustSPA.Affiliated.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:49:36.942457+00:00
-- url     : https://prove2.me/submissions/272db385-a7c5-4c91-b829-d62129a48864

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting
import Theorems.Thm_RobustSPA_Affiliated_lemma_1
import Theorems.Thm_RobustSPA_Affiliated_nature_step_aff
import Theorems.Thm_RobustSPA_Affiliated_pointwise_bound_aff
import Theorems.Thm_RobustSPA_Affiliated_regret_Fstar_eq
import Theorems.Thm_RobustSPA_Affiliated_Fiid_subset_Faff
import Theorems.Thm_RobustSPA_IID_SPA_isDSIC
import Theorems.Thm_RobustSPA_IID_step_2_seller
import Theorems.Thm_RobustSPA_IID_proposition_A_3_phi

open MeasureTheory Set RobustSPA.IID RobustSPA.Affiliated
open scoped Classical

namespace RAffRF

variable {n : ℕ}

lemma isWinner_unique {v : Fin n → ℝ} {i j : Fin n} (hi : isWinner v i) (hj : isWinner v j) :
    i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := hj.2 i h; have := hi.1 j; linarith
  · exact h
  · have := hi.2 j h; have := hj.1 i; linarith

/-- the highest competing valuation -/
noncomputable def cmax (v : Fin n → ℝ) (i : Fin n) : ℝ := ⨆ j : {j : Fin n // j ≠ i}, v j

lemma le_cmax (v : Fin n → ℝ) (i j : Fin n) (hj : j ≠ i) : v j ≤ cmax v i :=
  le_ciSup (f := fun j : {j : Fin n // j ≠ i} => v j) (Finite.bddAbove_range _) ⟨j, hj⟩

lemma le_second (v : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) : min (v a) (v b) ≤ second v :=
  le_ciSup (f := fun q : {q : Fin n × Fin n // q.1 ≠ q.2} => min (v q.1.1) (v q.1.2))
    (Finite.bddAbove_range _) ⟨(a, b), hab⟩

lemma second_eq_cmax {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) : second v = cmax v i := by
  by_cases hne : Nonempty {j : Fin n // j ≠ i}
  · obtain ⟨⟨j0, hj0⟩⟩ := hne
    haveI : Nonempty {q : Fin n × Fin n // q.1 ≠ q.2} := ⟨⟨(i, j0), fun h => hj0 h.symm⟩⟩
    haveI : Nonempty {j : Fin n // j ≠ i} := ⟨⟨j0, hj0⟩⟩
    apply le_antisymm
    · apply ciSup_le
      rintro ⟨⟨a, b⟩, hab⟩
      by_cases ha : a = i
      · subst ha
        exact (min_le_right _ _).trans (le_cmax v a b (Ne.symm hab))
      · exact (min_le_left _ _).trans (le_cmax v i a ha)
    · apply ciSup_le
      rintro ⟨j, hj⟩
      have h1 : min (v i) (v j) = v j := min_eq_right (hw.1 j)
      calc v j = min (v i) (v j) := h1.symm
        _ ≤ second v := le_second v i j (fun h => hj h.symm)
  · haveI h1 : IsEmpty {j : Fin n // j ≠ i} := not_nonempty_iff.mp hne
    haveI h2 : IsEmpty {q : Fin n × Fin n // q.1 ≠ q.2} := by
      constructor
      rintro ⟨⟨a, b⟩, hab⟩
      by_cases ha : a = i
      · subst ha; exact h1.false ⟨b, Ne.symm hab⟩
      · exact h1.false ⟨a, ha⟩
    unfold second cmax
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]

lemma cmax_le_of_winner {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) (h0 : 0 ≤ v i) :
    cmax v i ≤ v i := by
  by_cases hne : Nonempty {j : Fin n // j ≠ i}
  · exact ciSup_le (fun j => hw.1 j)
  · haveI : IsEmpty {j : Fin n // j ≠ i} := not_nonempty_iff.mp hne
    unfold cmax; rw [Real.iSup_of_isEmpty]; exact h0

lemma second_nonneg {v : Fin n → ℝ} (hv : v ∈ cube n) : 0 ≤ second v := by
  by_cases hne : Nonempty {q : Fin n × Fin n // q.1 ≠ q.2}
  · obtain ⟨⟨⟨a, b⟩, hab⟩⟩ := hne
    refine le_trans ?_ (le_second v a b hab)
    exact le_min (hv a (Set.mem_univ _)).1 (hv b (Set.mem_univ _)).1
  · haveI : IsEmpty {q : Fin n × Fin n // q.1 ≠ q.2} := not_nonempty_iff.mp hne
    unfold second; rw [Real.iSup_of_isEmpty]

lemma second_le_one {v : Fin n → ℝ} (hv : v ∈ cube n) : second v ≤ 1 := by
  unfold second
  apply Real.iSup_le _ zero_le_one
  rintro ⟨⟨a, b⟩, _⟩
  exact (min_le_left _ _).trans (hv a (Set.mem_univ _)).2

lemma meas_second : Measurable (fun v : Fin n → ℝ => second v) := by
  unfold second
  exact Measurable.iSup (fun q => (measurable_pi_apply _).min (measurable_pi_apply _))

lemma exists_winner (hn : 0 < n) (v : Fin n → ℝ) : ∃ i, isWinner v i := by
  obtain ⟨i1, _, hi1⟩ := Finset.exists_max_image Finset.univ v ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let S := Finset.univ.filter (fun i => ∀ j, v j ≤ v i)
  have hS : S.Nonempty := ⟨i1, by simp [S]; exact fun j => hi1 j (Finset.mem_univ _)⟩
  refine ⟨S.min' hS, ?_, ?_⟩
  · have := S.min'_mem hS
    simp only [S, Finset.mem_filter] at this
    exact this.2
  · intro j hj
    by_contra hcon
    push_neg at hcon
    have hmem := S.min'_mem hS
    simp only [S, Finset.mem_filter] at hmem
    have hjS : j ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro k; exact (hmem.2 k).trans hcon
    exact absurd (S.min'_le j hjS) (not_le.2 hj)

lemma top_eq_of_winner {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) : top v = v i := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  exact le_antisymm (ciSup_le hw.1) (le_ciSup (Finite.bddAbove_range v) i)


lemma sum_p_SPA (ρ : Measure ℝ) {v : Fin n → ℝ} {i : Fin n} (hw : isWinner v i) :
    ∑ j, (SPA (n := n) ρ).p j v =
      ∫ q, (Set.Iic (v i)).indicator (fun q => max (second v) q) q ∂ρ := by
  rw [Finset.sum_eq_single i (fun j _ hj => by
        show (if isWinner v j then _ else _) = _
        rw [if_neg (fun hw' => hj (isWinner_unique hw' hw))])
        (fun h => absurd (Finset.mem_univ i) h)]
  show (if isWinner v i then _ else _) = _
  rw [if_pos hw]

lemma top_nonneg {v : Fin n → ℝ} (hn : 0 < n) (hv : v ∈ cube n) : 0 ≤ top v := by
  obtain ⟨i, hw⟩ := exists_winner hn v
  rw [top_eq_of_winner hw]; exact (hv i (Set.mem_univ _)).1

lemma top_le_one {v : Fin n → ℝ} (hn : 0 < n) (hv : v ∈ cube n) : top v ≤ 1 := by
  obtain ⟨i, hw⟩ := exists_winner hn v
  rw [top_eq_of_winner hw]; exact (hv i (Set.mem_univ _)).2

lemma second_le_top {v : Fin n → ℝ} (hn : 0 < n) (hv : v ∈ cube n) : second v ≤ top v := by
  obtain ⟨i, hw⟩ := exists_winner hn v
  rw [top_eq_of_winner hw, second_eq_cmax hw]
  exact cmax_le_of_winner hw (hv i (Set.mem_univ _)).1

lemma meas_top : Measurable (fun v : Fin n → ℝ => top v) := by
  unfold top
  exact Measurable.iSup (fun i => measurable_pi_apply i)

/-- length of `(y, x] ∩ [q, ∞)` -/
lemma inner_vol (y x q : ℝ) (hyx : y ≤ x) :
    ∫ t in Set.Ioc y x, (Set.Ici q).indicator (fun _ => (1 : ℝ)) t =
      (Set.Iic x).indicator (fun q => x - max y q) q := by
  rw [integral_indicator_const _ measurableSet_Ici, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply measurableSet_Ici]
  by_cases hqx : q ≤ x
  · rw [Set.indicator_of_mem (show q ∈ Set.Iic x from hqx)]
    by_cases hqy : q ≤ y
    · have : Set.Ici q ∩ Set.Ioc y x = Set.Ioc y x := by
        ext t; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨le_trans hqy h.1.le, h⟩
      rw [this, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
        max_eq_left hqy]
    · push_neg at hqy
      have : Set.Ici q ∩ Set.Ioc y x = Set.Icc q x := by
        ext t; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
        constructor
        · exact fun h => ⟨h.1, h.2.2⟩
        · exact fun h => ⟨h.1, lt_of_lt_of_le hqy h.1, h.2⟩
      rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
        max_eq_right hqy.le]
  · rw [Set.indicator_of_notMem (show q ∉ Set.Iic x from hqx)]
    push_neg at hqx
    have : Set.Ici q ∩ Set.Ioc y x = ∅ := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h1 _ h2; linarith
    rw [this, measure_empty, ENNReal.toReal_zero]

/-- Payment of the winner: `E_q[max(y,q) 1(q ≤ x)] = x Φ(x) - ∫_y^x Φ`. -/
lemma pay_formula (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (y x : ℝ) (hyx : y ≤ x) :
    ∫ q, (Set.Iic x).indicator (fun q => max y q) q ∂ρ =
      x * (ρ (Set.Iic x)).toReal - ∫ t in y..x, (ρ (Set.Iic t)).toReal := by
  have hpt : ∀ q, (Set.Iic x).indicator (fun q => max y q) q =
      x * (Set.Iic x).indicator (fun _ => (1 : ℝ)) q -
        ∫ t in Set.Ioc y x, (Set.Ici q).indicator (fun _ => (1 : ℝ)) t := by
    intro q
    rw [inner_vol y x q hyx]
    by_cases hq : q ∈ Set.Iic x
    · simp [Set.indicator_of_mem hq]
    · simp [Set.indicator_of_notMem hq]
  simp_rw [hpt]
  -- Fubini
  have hF : Integrable (Function.uncurry fun (q t : ℝ) => (Set.Ici q).indicator (fun _ => (1 : ℝ)) t)
      (ρ.prod (volume.restrict (Set.Ioc y x))) := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
    have heq : (Function.uncurry fun (q t : ℝ) => (Set.Ici q).indicator (fun _ => (1 : ℝ)) t) =
        {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun _ => (1 : ℝ)) := by
      ext ⟨q, t⟩
      simp only [Function.uncurry_apply_pair, Set.indicator, Set.mem_Ici, Set.mem_setOf_eq]
    rw [heq]
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc y x)) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
    exact (integrable_const (1 : ℝ)).indicator hset
  have hI1 : Integrable (fun q => x * (Set.Iic x).indicator (fun _ => (1 : ℝ)) q) ρ :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iic).const_mul x
  have hI2 : Integrable (fun q => ∫ t in Set.Ioc y x, (Set.Ici q).indicator (fun _ => (1 : ℝ)) t) ρ :=
    hF.integral_prod_left
  rw [integral_sub hI1 hI2, integral_const_mul, integral_indicator_const _ measurableSet_Iic,
    smul_eq_mul, mul_one, integral_integral_swap hF, intervalIntegral.integral_of_le hyx]
  congr 1
  refine setIntegral_congr_fun (measurableSet_Ioc (a := y) (b := x)) fun t _ => ?_
  have : (fun q => (Set.Ici q).indicator (fun _ => (1 : ℝ)) t) = (Set.Iic t).indicator (fun _ => (1 : ℝ)) := by
    ext q; simp [Set.indicator]
  rw [this, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one, Measure.real]

/-- Pointwise regret of `SPA(ρ)`. -/
lemma pointwise_regret (hn : 0 < n) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (v : Fin n → ℝ) (hv : v ∈ cube n) :
    top v - ∑ i, (SPA (n := n) ρ).p i v =
      top v - top v * (ρ (Set.Iic (top v))).toReal + ∫ t in second v..top v, (ρ (Set.Iic t)).toReal := by
  obtain ⟨i, hw⟩ := exists_winner hn v
  rw [sum_p_SPA ρ hw, ← top_eq_of_winner hw, pay_formula ρ _ _ (second_le_top hn hv)]
  ring

/-- Hypotheses on the reserve CDF used for the regret formula. -/
structure PhiHyp (n : ℕ) (r : ℝ) (Φ : ℝ → ℝ) : Prop where
  hn : 0 < n
  hr0 : 0 < r
  hr1 : r < 1
  zero : ∀ t ≤ r, Φ t = 0
  nonneg : ∀ t, 0 ≤ Φ t
  le_one : ∀ t, Φ t ≤ 1
  meas : Measurable Φ
  cont : ContinuousOn Φ (Set.Icc r 1)
  deriv : ∀ t ∈ Set.Ioo r 1, HasDerivAt Φ (1 / t - ((n : ℝ) - 1) * r / (t * (t - r)) * Φ t) t
  bd : ∀ t ∈ Set.Ioc r 1, Φ t ≤ (t - r) / (n * r)

/-- derivative of `t (1 - Φ t)` (piecewise) -/
noncomputable def hp (n : ℕ) (r : ℝ) (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ r then 1 else if t ≤ 1 then (((n : ℝ) - 1) * r / (t - r) - 1) * Φ t else 0

lemma hp_meas {r : ℝ} {Φ : ℝ → ℝ} (H : PhiHyp n r Φ) : Measurable (hp n r Φ) := by
  unfold hp
  refine Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic ?_ measurable_const)
  exact ((measurable_const.mul measurable_const).div (measurable_id.sub measurable_const)
    |>.sub measurable_const).mul H.meas

lemma hp_bound {r : ℝ} {Φ : ℝ → ℝ} (H : PhiHyp n r Φ) (t : ℝ) : |hp n r Φ t| ≤ 2 := by
  unfold hp
  split_ifs with h1 h2
  · norm_num
  · push_neg at h1
    have hd : 0 < t - r := by linarith
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
    have hΦ0 := H.nonneg t
    have hΦ1 := H.le_one t
    have hb := H.bd t ⟨h1, h2⟩
    have hq : ((n : ℝ) - 1) * r / (t - r) * Φ t ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hd]
      rw [le_div_iff₀ (by have := H.hr0; positivity)] at hb
      have : ((n : ℝ) - 1) * r * Φ t * n ≤ (t - r) * n := by nlinarith [H.hr0]
      nlinarith
    have hq0 : 0 ≤ ((n : ℝ) - 1) * r / (t - r) * Φ t :=
      mul_nonneg (div_nonneg (mul_nonneg (by linarith) H.hr0.le) hd.le) hΦ0
    rw [abs_le]; constructor <;> nlinarith
  · norm_num

/-- FTC: `∫_0^x hp = x (1 - Φ x)` on `[0,1]`. -/
lemma hp_ftc {r : ℝ} {Φ : ℝ → ℝ} (H : PhiHyp n r Φ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ t in (0 : ℝ)..x, hp n r Φ t = x * (1 - Φ x) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (hp n r Φ) volume a b := by
    intro a b
    refine (intervalIntegrable_iff).mpr ?_
    refine Measure.integrableOn_of_bounded (M := 2) (by simp) (hp_meas H).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hp_bound H t
  have h0r : ∀ y, 0 ≤ y → y ≤ r → ∫ t in (0 : ℝ)..y, hp n r Φ t = y := by
    intro y hy0 hyr
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun t ht => ?_)]
    · simp
    · rw [Set.uIcc_of_le hy0] at ht
      simp [hp, show t ≤ r from le_trans ht.2 hyr]
  by_cases hxr : x ≤ r
  · rw [h0r x hx.1 hxr, H.zero x hxr]; ring
  · push_neg at hxr
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 r) (hint r x),
      h0r r H.hr0.le le_rfl]
    have hftc : ∫ t in r..x, hp n r Φ t = x * (1 - Φ x) - r * (1 - Φ r) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxr.le
      · exact (continuousOn_id.mul (continuousOn_const.sub
          (H.cont.mono (Set.Icc_subset_Icc le_rfl hx.2))))
      · intro t ht
        have ht1 : t ∈ Set.Ioo r 1 := ⟨ht.1, lt_of_lt_of_le ht.2 hx.2⟩
        have hd := H.deriv t ht1
        have h : HasDerivAt (fun x => x * (1 - Φ x))
            (1 * (1 - Φ t) + t * (0 - (1 / t - ((n : ℝ) - 1) * r / (t * (t - r)) * Φ t))) t :=
          (hasDerivAt_id' t).mul ((hasDerivAt_const t (1 : ℝ)).sub hd)
        have htr : t - r ≠ 0 := by linarith [ht.1]
        have ht0 : t ≠ 0 := by linarith [ht.1, H.hr0]
        refine h.congr_deriv ?_
        unfold hp
        rw [if_neg (not_le.mpr ht.1), if_pos ht1.2.le]
        field_simp
        ring
      · exact hint r x
    rw [hftc, H.zero r le_rfl]; ring

lemma hp_ind {r : ℝ} {Φ : ℝ → ℝ} (H : PhiHyp n r Φ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ t in Set.Icc (0 : ℝ) 1, (Set.Iio x).indicator (hp n r Φ) t = x * (1 - Φ x) := by
  rw [setIntegral_indicator measurableSet_Iio]
  have : Set.Icc (0 : ℝ) 1 ∩ Set.Iio x = Set.Ico 0 x := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, by linarith [hx.2]⟩, h.2⟩
  rw [this, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.1, hp_ftc H x hx]

lemma phi_ind {Φ : ℝ → ℝ} (y x : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x ≤ 1) :
    ∫ t in Set.Icc (0 : ℝ) 1, (Set.Ico y x).indicator Φ t = ∫ t in y..x, Φ t := by
  rw [setIntegral_indicator measurableSet_Ico]
  have : Set.Icc (0 : ℝ) 1 ∩ Set.Ico y x = Set.Ico y x := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨⟨by linarith [h.1], by linarith [h.2]⟩, h⟩
  rw [this, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hyx]

lemma F1_mono' (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] : Monotone (F1 μ) := by
  intro a b hab
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono fun u hu => le_trans hu hab

lemma F2_mono' (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] : Monotone (F2 μ) := by
  intro a b hab
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono fun u hu => le_trans hu hab

lemma toReal_le_one' {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Set α) : (μ s).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := μ) (s := s))

lemma intOn_Icc {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ t, |f t| ≤ C) :
    IntegrableOn f (Set.Icc (0 : ℝ) 1) :=
  Measure.integrableOn_of_bounded (M := C) (by simp) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hC t)

/-- The regret formula (Regret-F of Proposition 1 with (ODE-Φ) substituted). -/
theorem regret_formula {r : ℝ} {Φ : ℝ → ℝ} (H : PhiHyp n r Φ) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hρ : ∀ t, (ρ (Set.Iic t)).toReal = Φ t)
    (μ : Measure (Fin n → ℝ)) (hμ : μ ∈ Fall n) :
    regret (SPA ρ) μ = r - (∫ t in (0 : ℝ)..r, F1 μ t) +
      ∫ t in r..1, ((((n : ℝ) - 1) * r / (t - r) - 1) * Φ t * (1 - F1 μ t) +
        Φ t * (F2 μ t - F1 μ t)) := by
  haveI := hμ.1
  have hn := H.hn
  have hae : ∀ᵐ v ∂μ, v ∈ cube n := by
    rw [ae_iff]; simpa [Set.compl_def] using hμ.2
  set k : (Fin n → ℝ) → ℝ → ℝ := fun v t =>
    (Set.Iio (top v)).indicator (hp n r Φ) t + (Set.Ico (second v) (top v)).indicator Φ t with hk
  have hΦb : ∀ t, |Φ t| ≤ 1 := fun t => by
    rw [abs_le]; exact ⟨by linarith [H.nonneg t], H.le_one t⟩
  have hind1 : ∀ x : ℝ, ∀ t, |(Set.Iio x).indicator (hp n r Φ) t| ≤ 2 := fun x t => by
    by_cases ht : t ∈ Set.Iio x
    · rw [Set.indicator_of_mem ht]; exact hp_bound H t
    · rw [Set.indicator_of_notMem ht]; norm_num
  have hind2 : ∀ y x : ℝ, ∀ t, |(Set.Ico y x).indicator Φ t| ≤ 1 := fun y x t => by
    by_cases ht : t ∈ Set.Ico y x
    · rw [Set.indicator_of_mem ht]; exact hΦb t
    · rw [Set.indicator_of_notMem ht]; norm_num
  -- pointwise identity
  have hpt : ∀ v ∈ cube n, top v - ∑ i, (SPA (n := n) ρ).p i v = ∫ t in Set.Icc (0 : ℝ) 1, k v t := by
    intro v hv
    have h0 := top_nonneg hn hv
    have h1 := top_le_one hn hv
    have hs0 := second_nonneg hv
    have hst := second_le_top hn hv
    rw [pointwise_regret hn ρ v hv]
    simp only [hk]
    rw [integral_add (intOn_Icc ((hp_meas H).indicator measurableSet_Iio) 2 (hind1 _))
      (intOn_Icc (H.meas.indicator measurableSet_Ico) 1 (hind2 _ _)),
      hp_ind H (top v) ⟨h0, h1⟩, phi_ind _ _ hs0 hst h1]
    simp_rw [hρ]
    ring
  -- Fubini
  have hmeas_k : Measurable (Function.uncurry k) := by
    have e1 : (fun p : (Fin n → ℝ) × ℝ => (Set.Iio (top p.1)).indicator (hp n r Φ) p.2) =
        fun p => if p.2 < top p.1 then hp n r Φ p.2 else 0 := by
      ext p; simp [Set.indicator_apply]
    have e2 : (fun p : (Fin n → ℝ) × ℝ => (Set.Ico (second p.1) (top p.1)).indicator Φ p.2) =
        fun p => if second p.1 ≤ p.2 ∧ p.2 < top p.1 then Φ p.2 else 0 := by
      ext p; simp [Set.indicator_apply]
    have m1 : Measurable (fun p : (Fin n → ℝ) × ℝ => (Set.Iio (top p.1)).indicator (hp n r Φ) p.2) := by
      rw [e1]
      exact Measurable.ite (measurableSet_lt measurable_snd (meas_top.comp measurable_fst))
        ((hp_meas H).comp measurable_snd) measurable_const
    have m2 : Measurable (fun p : (Fin n → ℝ) × ℝ =>
        (Set.Ico (second p.1) (top p.1)).indicator Φ p.2) := by
      rw [e2]
      exact Measurable.ite ((measurableSet_le (meas_second.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (meas_top.comp measurable_fst)))
        (H.meas.comp measurable_snd) measurable_const
    exact m1.add m2
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [isFiniteMeasure_restrict]; simp
  have hint_k : Integrable (Function.uncurry k) (μ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    refine Integrable.of_bound hmeas_k.aestronglyMeasurable 3 (Filter.Eventually.of_forall ?_)
    rintro ⟨v, t⟩
    simp only [Function.uncurry_apply_pair, hk, Real.norm_eq_abs]
    calc |(Set.Iio (top v)).indicator (hp n r Φ) t + (Set.Ico (second v) (top v)).indicator Φ t|
        ≤ |(Set.Iio (top v)).indicator (hp n r Φ) t| + |(Set.Ico (second v) (top v)).indicator Φ t| :=
          abs_add_le _ _
      _ ≤ 2 + 1 := add_le_add (hind1 _ _) (hind2 _ _ _)
      _ = 3 := by norm_num
  -- inner integrals
  have hinner : ∀ t, ∫ v, k v t ∂μ = hp n r Φ t * (1 - F1 μ t) + Φ t * (F2 μ t - F1 μ t) := by
    intro t
    have e1 : (fun v => (Set.Iio (top v)).indicator (hp n r Φ) t) =
        {v : Fin n → ℝ | top v ≤ t}ᶜ.indicator (fun _ => hp n r Φ t) := by
      ext v; simp [Set.indicator_apply]
    have e2 : (fun v => (Set.Ico (second v) (top v)).indicator Φ t) =
        ({v : Fin n → ℝ | second v ≤ t} \ {v | top v ≤ t}).indicator (fun _ => Φ t) := by
      ext v; simp [Set.indicator_apply]
    have mA : MeasurableSet {v : Fin n → ℝ | second v ≤ t} := measurableSet_le meas_second measurable_const
    have mB : MeasurableSet {v : Fin n → ℝ | top v ≤ t} := measurableSet_le meas_top measurable_const
    have e3 : (fun v => k v t) = fun v => {v : Fin n → ℝ | top v ≤ t}ᶜ.indicator
        (fun _ => hp n r Φ t) v +
        ({v : Fin n → ℝ | second v ≤ t} \ {v | top v ≤ t}).indicator (fun _ => Φ t) v := by
      ext v
      simp only [hk]
      rw [← congrFun e1 v, ← congrFun e2 v]
    rw [e3, integral_add ((integrable_const _).indicator mB.compl)
      ((integrable_const _).indicator (mA.diff mB)), integral_indicator_const _ mB.compl,
      integral_indicator_const _ (mA.diff mB)]
    have c1 : μ.real {v : Fin n → ℝ | top v ≤ t}ᶜ = 1 - F1 μ t := by
      rw [Measure.real, prob_compl_eq_one_sub mB, ENNReal.toReal_sub_of_le prob_le_one
        ENNReal.one_ne_top, ENNReal.toReal_one]
      rfl
    have hBA : μ ({v : Fin n → ℝ | top v ≤ t} \ {v | second v ≤ t}) = 0 := by
      apply measure_mono_null _ hμ.2
      intro v hv hvc
      exact hv.2 (le_trans (second_le_top hn hvc) hv.1)
    have hsplitA := measure_diff_add_inter (μ := μ) {v : Fin n → ℝ | second v ≤ t} mB
    have hsplitB := measure_inter_add_diff (μ := μ) {v : Fin n → ℝ | top v ≤ t} mA
    rw [hBA, add_zero, Set.inter_comm] at hsplitB
    rw [hsplitB] at hsplitA
    have c2 : μ.real ({v : Fin n → ℝ | second v ≤ t} \ {v | top v ≤ t}) = F2 μ t - F1 μ t := by
      have := congrArg ENNReal.toReal hsplitA
      rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
      simp only [Measure.real, F1, F2]
      linarith
    rw [c1, c2, smul_eq_mul, smul_eq_mul]
    ring
  -- assemble
  have hreg : regret (SPA ρ) μ = ∫ t in Set.Icc (0 : ℝ) 1,
      (hp n r Φ t * (1 - F1 μ t) + Φ t * (F2 μ t - F1 μ t)) := by
    unfold regret
    rw [integral_congr_ae (hae.mono fun v hv => hpt v hv), integral_integral_swap hint_k]
    exact setIntegral_congr_fun measurableSet_Icc fun t _ => hinner t
  rw [hreg, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  set g : ℝ → ℝ := fun t => hp n r Φ t * (1 - F1 μ t) + Φ t * (F2 μ t - F1 μ t) with hg
  have hgm : Measurable g := by
    exact ((hp_meas H).mul (measurable_const.sub (F1_mono' μ).measurable)).add
      (H.meas.mul ((F2_mono' μ).measurable.sub (F1_mono' μ).measurable))
  have hgb : ∀ t, |g t| ≤ 4 := by
    intro t
    have a1 := hp_bound H t
    have a2 := hΦb t
    have f1 : 0 ≤ F1 μ t := ENNReal.toReal_nonneg
    have f1' : F1 μ t ≤ 1 := toReal_le_one' μ _
    have f2 : 0 ≤ F2 μ t := ENNReal.toReal_nonneg
    have f2' : F2 μ t ≤ 1 := toReal_le_one' μ _
    simp only [hg]
    calc |hp n r Φ t * (1 - F1 μ t) + Φ t * (F2 μ t - F1 μ t)|
        ≤ |hp n r Φ t * (1 - F1 μ t)| + |Φ t * (F2 μ t - F1 μ t)| := abs_add_le _ _
      _ = |hp n r Φ t| * |1 - F1 μ t| + |Φ t| * |F2 μ t - F1 μ t| := by rw [abs_mul, abs_mul]
      _ ≤ 2 * 1 + 1 * 1 := by
          apply add_le_add
          · exact mul_le_mul a1 (by rw [abs_le]; constructor <;> linarith) (abs_nonneg _) (by norm_num)
          · exact mul_le_mul a2 (by rw [abs_le]; constructor <;> linarith) (abs_nonneg _) (by norm_num)
      _ ≤ 4 := by norm_num
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    refine (intervalIntegrable_iff).mpr ?_
    exact Measure.integrableOn_of_bounded (M := 4) (by simp) hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hgb t)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hgi 0 r) (hgi r 1)]
  have hpart1 : ∫ t in (0 : ℝ)..r, g t = r - ∫ t in (0 : ℝ)..r, F1 μ t := by
    rw [intervalIntegral.integral_congr (g := fun t => 1 - F1 μ t) (fun t ht => ?_)]
    · rw [intervalIntegral.integral_sub intervalIntegrable_const
        ((F1_mono' μ).intervalIntegrable)]
      simp
    · rw [Set.uIcc_of_le H.hr0.le] at ht
      simp only [hg, hp, if_pos ht.2, H.zero t ht.2]
      ring
  have hpart2 : ∫ t in r..1, g t = ∫ t in r..1, ((((n : ℝ) - 1) * r / (t - r) - 1) * Φ t *
      (1 - F1 μ t) + Φ t * (F2 μ t - F1 μ t)) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le H.hr1.le] at ht
    simp only [hg, hp, if_neg (not_le.mpr ht.1), if_pos ht.2]
  rw [hpart1, hpart2]

/-- The facts about `Φ*_n` needed for the regret formula, from Proposition A-3. -/
lemma phiHyp_of (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (ρ : ProbabilityMeasure ℝ) (hρ : ∀ t, cdfOf ρ t = PhiStar n r t) :
    PhiHyp n r (PhiStar n r) := by
  obtain ⟨hS, hD, hT, _⟩ := proposition_A_3_phi n hn r hr hrEq
  have hr0 := hr.1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : r < 1 := by
    have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hnR
    linarith [hr.2]
  have hcdf : ∀ t, PhiStar n r t = ((ρ : Measure ℝ) (Set.Iic t)).toReal := fun t => (hρ t).symm
  refine ⟨hn, hr0, hr1, fun t ht => by simp [PhiStar, ht], fun t => by rw [hcdf]; positivity,
    fun t => by rw [hcdf]; exact toReal_le_one' _ _, ?_, ?_, hD, ?_⟩
  · have : PhiStar n r = fun t => ((ρ : Measure ℝ) (Set.Iic t)).toReal := funext hcdf
    rw [this]
    apply Monotone.measurable
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr hab))
  · -- continuity on `[r, 1]`
    set g : ℝ → ℝ := fun v => (v / (v - r)) ^ (n - 1) * Real.log (v / r) -
      ∑ k ∈ Finset.Ico 1 n, (1 / (k : ℝ)) * (v / (v - r)) ^ (n - 1 - k) with hg
    have hdiv : ContinuousOn (fun v : ℝ => v / (v - r)) (Set.Ioi r) :=
      continuousOn_id.div (continuousOn_id.sub continuousOn_const)
        (fun x hx => sub_ne_zero.mpr (ne_of_gt hx))
    have hgc : ContinuousOn g (Set.Ioi r) := by
      apply ContinuousOn.sub
      · apply ContinuousOn.mul (hdiv.pow _)
        apply ContinuousOn.log (continuousOn_id.div_const r)
        intro x hx
        have : 0 < x := lt_trans hr0 hx
        exact div_ne_zero this.ne' hr0.ne'
      · apply continuousOn_finset_sum
        intro k _
        exact continuousOn_const.mul (hdiv.pow _)
    have hPg : ∀ v ∈ Set.Ioc r 1, PhiStar n r v = g v := by
      intro v hv
      simp only [PhiStar, if_neg (not_le.mpr hv.1), if_pos hv.2, hg]
    have hPc : ContinuousOn (PhiStar n r) (Set.Ioc r 1) :=
      (hgc.mono Set.Ioc_subset_Ioi_self).congr hPg
    intro x hx
    rcases eq_or_lt_of_le hx.1 with hxr | hxr
    · subst hxr
      have h0 : PhiStar n r r = 0 := by simp [PhiStar]
      have hw : ContinuousWithinAt (PhiStar n r) (Set.Ioi r) r := by
        rw [ContinuousWithinAt, h0]; exact hT
      exact (continuousWithinAt_Ioi_iff_Ici.mp hw).mono Set.Icc_subset_Ici_self
    · have hmem : Set.Ioc r 1 ∈ nhdsWithin x (Set.Icc r 1) :=
        mem_nhdsWithin.mpr ⟨Set.Ioi r, isOpen_Ioi, hxr, fun y hy => ⟨hy.1, hy.2.2⟩⟩
      exact (hPc x ⟨hxr, hx.2⟩).mono_of_mem_nhdsWithin hmem
  · -- the bound from the series
    intro v hv
    have hS' := hS v hv
    have hv0 : 0 < v := lt_trans hr0 hv.1
    set x := (v - r) / v with hx
    have hx0 : 0 ≤ x := div_nonneg (by linarith [hv.1]) hv0.le
    have hx1 : x < 1 := by rw [hx, div_lt_one hv0]; linarith
    have hnR' : (0 : ℝ) < n := by linarith
    have hgeo : HasSum (fun j : ℕ => (x / n) * x ^ j) ((x / n) * (1 - x)⁻¹) :=
      (hasSum_geometric_of_lt_one hx0 hx1).mul_left _
    have hle := hasSum_le (fun j => ?_) hS' hgeo
    · have h1x : 1 - x = r / v := by rw [hx]; field_simp; ring
      calc PhiStar n r v ≤ (x / n) * (1 - x)⁻¹ := hle
        _ = (v - r) / (n * r) := by rw [h1x, hx]; field_simp
    · have hjn : (n : ℝ) ≤ ((j + n : ℕ) : ℝ) := by push_cast; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
      have hxj : 0 ≤ x ^ (j + 1) := pow_nonneg hx0 _
      calc 1 / ((j + n : ℕ) : ℝ) * x ^ (j + 1) ≤ 1 / (n : ℝ) * x ^ (j + 1) :=
            mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hnR' hjn) hxj
        _ = (x / n) * x ^ j := by rw [pow_succ]; ring

/-- One buyer: the regret of `SPA(Φ*_1)` is at most `r` against every law on `[0,1]`. -/
lemma part1_one (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / ((1 : ℕ) : ℝ))) (hrEq : rEq 1 r = 0)
    (ρ : ProbabilityMeasure ℝ) (hρ : ∀ t, cdfOf ρ t = PhiStar 1 r t)
    (μ : Measure (Fin 1 → ℝ)) (hμ : μ ∈ Fall 1) : regret (SPA (ρ : Measure ℝ)) μ ≤ r := by
  have H := phiHyp_of (n := 1) one_pos r hr hrEq ρ hρ
  haveI : IsProbabilityMeasure μ := hμ.1
  rw [regret_formula H (ρ : Measure ℝ) hρ μ hμ]
  have hsec : ∀ u : Fin 1 → ℝ, second u = 0 := by
    intro u
    haveI : IsEmpty {q : Fin 1 × Fin 1 // q.1 ≠ q.2} := ⟨fun q => q.2 (Subsingleton.elim _ _)⟩
    unfold second
    exact Real.iSup_of_isEmpty _
  have hzero : ∫ t in r..1, ((((1 : ℕ) : ℝ) - 1) * r / (t - r) - 1) * PhiStar 1 r t * (1 - F1 μ t) +
      PhiStar 1 r t * (F2 μ t - F1 μ t) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Set.uIoc_of_le H.hr1.le] at ht
      have ht0 : 0 ≤ t := le_of_lt (lt_trans H.hr0 ht.1)
      have hF2 : F2 μ t = 1 := by
        have hset : {u : Fin 1 → ℝ | second u ≤ t} = Set.univ := by
          ext u; simp [hsec u, ht0]
        simp only [F2]
        rw [hset, measure_univ, ENNReal.toReal_one]
      rw [hF2]
      simp only [Nat.cast_one, sub_self, zero_mul, zero_div]
      ring
  rw [hzero, add_zero]
  have : 0 ≤ ∫ t in (0 : ℝ)..r, F1 μ t :=
    intervalIntegral.integral_nonneg H.hr0.le fun t _ => ENNReal.toReal_nonneg
  linarith

end RAffRF

open RobustSPA.Affiliated

namespace RAffProp2Red

/-- Regret of a DSIC mechanism is bounded above uniformly over laws supported on the cube. -/
lemma regret_bdd {n : ℕ} (hn : 0 < n) (m : Mechanism n) (hm : m.IsDSIC) :
    ∃ C : ℝ, ∀ μ ∈ Fall n, regret m μ ≤ C := by
  obtain ⟨B, hB⟩ := hm.p_bdd
  refine ⟨1 + n * |B|, fun μ hμ => ?_⟩
  haveI := hμ.1
  have hae : ∀ᵐ v ∂μ, v ∈ cube n := by
    rw [ae_iff]
    simpa [Set.compl_def] using hμ.2
  have hC : 0 ≤ 1 + n * |B| := by positivity
  by_cases hint : Integrable (fun v => top v - ∑ i, m.p i v) μ
  · unfold regret
    calc ∫ v, (top v - ∑ i, m.p i v) ∂μ ≤ ∫ _v, (1 + n * |B|) ∂μ := by
          apply integral_mono_ae hint (integrable_const _)
          filter_upwards [hae] with v hv
          have htop : top v ≤ 1 := by
            haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
            exact ciSup_le fun i => (hv i (Set.mem_univ _)).2
          have hs : -(∑ i, m.p i v) ≤ n * |B| := by
            rw [← Finset.sum_neg_distrib]
            calc ∑ i, -m.p i v ≤ ∑ _i : Fin n, |B| := Finset.sum_le_sum fun i _ => by
                  have h1 := hB v hv i
                  have h2 := le_abs_self B
                  have h3 := neg_le_abs (m.p i v)
                  linarith
              _ = n * |B| := by simp
          linarith
      _ = 1 + n * |B| := by simp
  · unfold regret
    rw [integral_undef hint]
    exact hC

/-- The isorevenue law lives on `[0,1]`. -/
lemma G_supp (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (G : ProbabilityMeasure ℝ)
    (hG : ∀ t, cdfOf G t = isoCDF r t) : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0 := by
  have h0 : (G : Measure ℝ) (Set.Iic 0) = 0 := by
    have := hG 0
    simp only [cdfOf, isoCDF, if_pos hr0] at this
    rcases (ENNReal.toReal_eq_zero_iff _).mp this with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  have h1 : (G : Measure ℝ) (Set.Iic 1) = 1 := by
    have := hG 1
    simp only [cdfOf, isoCDF, if_neg (not_lt.mpr hr1.le), lt_irrefl, if_false] at this
    have hne : (G : Measure ℝ) (Set.Iic 1) ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hne, this, ENNReal.ofReal_one]
  have h2 : (G : Measure ℝ) (Set.Ioi 1) = 0 := by
    rw [← Set.compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic]
    exact h1
  have hsub : (Set.Icc (0 : ℝ) 1)ᶜ ⊆ Set.Iic 0 ∪ Set.Ioi 1 := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl (le_of_lt hx)
    · exact Or.inr hx
  apply le_antisymm _ bot_le
  calc (G : Measure ℝ) (Set.Icc 0 1)ᶜ ≤ (G : Measure ℝ) (Set.Iic 0 ∪ Set.Ioi 1) := measure_mono hsub
    _ ≤ (G : Measure ℝ) (Set.Iic 0) + (G : Measure ℝ) (Set.Ioi 1) := measure_union_le _ _
    _ = 0 := by rw [h0, h2, add_zero]

/-- For one buyer every law on the cube is (trivially) i.i.d. -/
lemma Fall_one_subset_Fiid (μ : Measure (Fin 1 → ℝ)) (hμ : μ ∈ Fall 1) : μ ∈ Fiid 1 := by
  haveI := hμ.1
  have hmeas : Measurable (fun v : Fin 1 → ℝ => v 0) := measurable_pi_apply 0
  let G : ProbabilityMeasure ℝ := ⟨μ.map (fun v => v 0), Measure.isProbabilityMeasure_map hmeas.aemeasurable⟩
  have hpre : ∀ s : Set ℝ, (fun v : Fin 1 → ℝ => v 0) ⁻¹' s = Set.univ.pi (fun _ : Fin 1 => s) := by
    intro s; ext v; simp [Fin.forall_fin_one]
  refine ⟨G, ?_, ?_⟩
  · show (μ.map (fun v => v 0)) (Set.Icc 0 1)ᶜ = 0
    rw [Measure.map_apply hmeas (measurableSet_Icc.compl), Set.preimage_compl, hpre]
    exact hμ.2
  · symm
    apply Measure.pi_eq
    intro s hs
    show μ (Set.univ.pi s) = ∏ i : Fin 1, (μ.map (fun v => v 0)) (s i)
    rw [Fin.prod_univ_one, Measure.map_apply hmeas (hs 0)]
    congr 1
    ext v; simp [Fin.forall_fin_one]

/-- Bounds `0 ≤ Φ*_n(v) ≤ (v - r)/(n r)` on `(r, 1]` from the series form of Proposition A-3. -/
lemma phi_bounds (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (v : ℝ) (hv : v ∈ Set.Ioc r 1) :
    0 ≤ PhiStar n r v ∧ PhiStar n r v ≤ (v - r) / (n * r) := by
  have hS := (proposition_A_3_phi n hn r hr hrEq).1 v hv
  have hr0 := hr.1
  have hv0 : 0 < v := lt_trans hr0 hv.1
  set x := (v - r) / v with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith [hv.1]) hv0.le
  have hx1 : x < 1 := by rw [hx, div_lt_one hv0]; linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact hS.nonneg fun j => by positivity
  · have hgeo : HasSum (fun j : ℕ => (x / n) * x ^ j) ((x / n) * (1 - x)⁻¹) :=
      (hasSum_geometric_of_lt_one hx0 hx1).mul_left _
    have hle := hasSum_le (fun j => ?_) hS hgeo
    · have h1x : 1 - x = r / v := by rw [hx]; field_simp; ring
      calc PhiStar n r v ≤ (x / n) * (1 - x)⁻¹ := hle
        _ = (v - r) / (n * r) := by rw [h1x, hx]; field_simp
    · have hjn : (n : ℝ) ≤ ((j + n : ℕ) : ℝ) := by push_cast; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
      have hxj : 0 ≤ x ^ (j + 1) := pow_nonneg hx0 _
      calc 1 / ((j + n : ℕ) : ℝ) * x ^ (j + 1) ≤ 1 / (n : ℝ) * x ^ (j + 1) :=
            mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hnR hjn) hxj
        _ = (x / n) * x ^ j := by rw [pow_succ]; ring

/-- The common bound on the integrands. -/
lemma integrand_bound (n : ℕ) (hn : 0 < n) (r p z w Φ : ℝ) (hr0 : 0 < r) (hp : p ∈ Set.Ioc r 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hw : w ∈ Set.Icc (0 : ℝ) 1) (hΦ0 : 0 ≤ Φ)
    (hΦ1 : Φ ≤ (p - r) / (n * r)) :
    |(((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z + (n : ℝ) * w) * Φ|
      ≤ 3 / r := by
  have hd : 0 < p - r := by linarith [hp.1]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set q := Φ / (p - r) with hq
  have hq0 : 0 ≤ q := div_nonneg hΦ0 hd.le
  have hq1 : q * (n * r) ≤ 1 := by
    rw [hq, div_mul_eq_mul_div, div_le_one hd]
    rw [le_div_iff₀ (by positivity)] at hΦ1
    linarith
  have hΦ : Φ = q * (p - r) := by rw [hq]; field_simp
  have heq : (((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z + (n : ℝ) * w) * Φ
      = q * (((n : ℝ) - 1) * r - (p - r) - ((n : ℝ) - 1) * p * z + n * (p - r) * w) := by
    rw [hΦ]; field_simp
  rw [heq, abs_mul, abs_of_nonneg hq0]
  have hp1 := hp.2
  have hbr : |((n : ℝ) - 1) * r - (p - r) - ((n : ℝ) - 1) * p * z + n * (p - r) * w| ≤ 3 * n := by
    rw [abs_le]
    have hr1 : r ≤ 1 := by linarith [hp.1]
    have e1 : 0 ≤ ((n : ℝ) - 1) * r := mul_nonneg (by linarith) hr0.le
    have e2 : ((n : ℝ) - 1) * r ≤ n := by nlinarith
    have e3 : 0 ≤ ((n : ℝ) - 1) * p * z := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hz.1
    have e4 : ((n : ℝ) - 1) * p * z ≤ n := by
      have : ((n : ℝ) - 1) * p ≤ n := by nlinarith
      nlinarith [hz.2, hz.1]
    have e5 : 0 ≤ n * (p - r) * w := mul_nonneg (mul_nonneg (by linarith) hd.le) hw.1
    have e6 : n * (p - r) * w ≤ n := by
      have : (n : ℝ) * (p - r) ≤ n := by nlinarith
      nlinarith [hw.2, hw.1]
    constructor <;> nlinarith
  have hr' : q ≤ 1 / (n * r) := by rw [le_div_iff₀ (by positivity)]; linarith
  calc q * |((n : ℝ) - 1) * r - (p - r) - ((n : ℝ) - 1) * p * z + n * (p - r) * w|
      ≤ (1 / (n * r)) * (3 * n) := mul_le_mul hr' hbr (abs_nonneg _) (by positivity)
    _ = 3 / r := by field_simp

lemma F1_mono {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] : Monotone (F1 μ) := by
  intro a b hab
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro u hu
  exact le_trans hu hab

lemma F1k_mono {n : ℕ} (k : ℕ) (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] :
    Monotone (F1k k μ) := by
  intro a b hab
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro u hu i hi
  exact le_trans (hu i hi) hab

lemma toReal_mem_Icc {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Set α) : (μ s).toReal ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, by
    have := prob_le_one (μ := μ) (s := s)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)⟩

/-- Integrability of the integrand `(c₁ - 1 - c₂ z(p) + n w(p)) Φ*(p)` on `[r, 1]`. -/
lemma integrand_ii (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (ρ : ProbabilityMeasure ℝ) (hρ : ∀ t, cdfOf ρ t = PhiStar n r t)
    (z w : ℝ → ℝ) (hzm : Measurable z) (hwm : Measurable w)
    (hz : ∀ p ∈ Set.Ioc r 1, z p ∈ Set.Icc (0 : ℝ) 1)
    (hw : ∀ p ∈ Set.Ioc r 1, w p ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun p => (((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z p +
        (n : ℝ) * w p) * PhiStar n r p) volume r 1 := by
  have hr1 : r ≤ 1 := by
    have h1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hn)]; exact_mod_cast hn
    linarith [hr.2]
  have hPhi : PhiStar n r = fun t => cdfOf ρ t := funext fun t => (hρ t).symm
  have hPm : Measurable (PhiStar n r) := by
    rw [hPhi]
    apply Monotone.measurable
    intro a b hab
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (Set.Iic_subset_Iic.mpr hab)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr1]
  apply Measure.integrableOn_of_bounded (M := 3 / r) (by simp)
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun p hp => ?_
    rw [Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := phi_bounds n hn r hr hrEq p hp
    exact integrand_bound n hn r p (z p) (w p) _ hr.1 hp (hz p hp) (hw p hp) h0 h1

end RAffProp2Red

open RAffProp2Red in
theorem solution (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (ρ : ProbabilityMeasure ℝ) (hρ : ∀ t, cdfOf ρ t = PhiStar n r t)
    (G : ProbabilityMeasure ℝ) (hG : ∀ t, cdfOf G t = isoCDF r t) :
    (∀ μ ∈ Faff n, regret (SPA (ρ : Measure ℝ)) μ ≤
        regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ))) ∧
    (∀ m : Mechanism n, m.IsDSIC →
        regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) ≤
          regret m (Measure.pi fun _ : Fin n => (G : Measure ℝ))) ∧
    minimaxRegret n (Faff n) = minimaxRegret n (Fiid n) := by
  have hr0 := hr.1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : r < 1 := by
    have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hnR
    linarith [hr.2]
  set Gn : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => (G : Measure ℝ) with hGn_def
  set S : Mechanism n := SPA (ρ : Measure ℝ) with hS_def
  have hS : S.IsDSIC := SPA_isDSIC n ρ
  have hGn_iid : Gn ∈ Fiid n := ⟨G, G_supp r hr0 hr1 G hG, rfl⟩
  have hGn_aff : Gn ∈ Faff n := Fiid_subset_Faff n hGn_iid
  -- Part 2: the seller's step
  have part2 : ∀ m : Mechanism n, m.IsDSIC → regret S Gn ≤ regret m Gn :=
    step_2_seller n hn r hr hrEq ρ G hρ hG
  -- Part 1: nature's step
  have part1 : ∀ μ ∈ Faff n, regret S μ ≤ regret S Gn := by
    intro μ hμ
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · -- n = 1: the regret is at most `r`, which is the regret at `F*_1`
      obtain rfl : n = 1 := by omega
      refine (RAffRF.part1_one r hr hrEq ρ hρ μ hμ.1.1).trans (le_of_eq ?_)
      rw [regret_Fstar_eq 1 hn r hr hrEq ρ hρ G hG]
      have : ∫ p in r..1, ((((1 : ℕ) : ℝ) - 1) * r / (p - r) - 1 -
          (((1 : ℕ) : ℝ) - 1) * p / (p - r) * (1 - r / p) ^ 1 + ((1 : ℕ) : ℝ) * (1 - r / p) ^ (1 - 1)) *
            PhiStar 1 r p = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun p _ => by simp)]
        simp
      rw [this, add_zero]
    · haveI : IsProbabilityMeasure μ := hμ.1.1.1
      have hns := nature_step_aff n hn2 r hr hrEq ρ hρ μ hμ
      have hst := regret_Fstar_eq n hn r hr hrEq ρ hρ G hG
      rw [hst]
      refine hns.trans (add_le_add le_rfl ?_)
      have hr1' : r ≤ 1 := hr1.le
      have hzF : ∀ p ∈ Set.Ioc r 1, (1 - r / p) ^ n ∈ Set.Icc (0 : ℝ) 1 ∧
          (1 - r / p) ^ (n - 1) ∈ Set.Icc (0 : ℝ) 1 := by
        intro p hp
        have hp0 : 0 < p := lt_trans hr0 hp.1
        have ha : 0 ≤ 1 - r / p := by
          rw [sub_nonneg, div_le_one hp0]; exact hp.1.le
        have hb : 1 - r / p ≤ 1 := by
          have : 0 ≤ r / p := div_nonneg hr0.le hp0.le
          linarith
        exact ⟨⟨pow_nonneg ha _, pow_le_one₀ ha hb⟩, ⟨pow_nonneg ha _, pow_le_one₀ ha hb⟩⟩
      apply intervalIntegral.integral_mono_on_of_le_Ioo hr1'
      · exact integrand_ii n hn r hr hrEq ρ hρ (F1 μ) (F1k (n - 1) μ)
          (F1_mono μ).measurable (F1k_mono _ μ).measurable
          (fun p _ => toReal_mem_Icc μ _) (fun p _ => toReal_mem_Icc μ _)
      · exact integrand_ii n hn r hr hrEq ρ hρ (fun p => (1 - r / p) ^ n)
          (fun p => (1 - r / p) ^ (n - 1)) (by fun_prop) (by fun_prop)
          (fun p hp => (hzF p hp).1) (fun p hp => (hzF p hp).2)
      · intro p hp
        have hp' : p ∈ Set.Ioc r 1 := ⟨hp.1, hp.2.le⟩
        have hΦ0 := (phi_bounds n hn r hr hrEq p hp').1
        apply mul_le_mul_of_nonneg_right _ hΦ0
        have hz := toReal_mem_Icc μ {u | top u ≤ p}
        have hw := toReal_mem_Icc μ {u : Fin n → ℝ | ∀ i : Fin n, (i : ℕ) < n - 1 → u i ≤ p}
        have hL := lemma_1 n hn2 μ hμ p
        have hFk : F1k (n - 1) μ p ≤ F1 μ p ^ (((n : ℝ) - 1) / (n : ℝ)) := by
          have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
            have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
            linarith
          have hw0 : 0 ≤ F1k (n - 1) μ p := hw.1
          have hz0 : 0 ≤ F1 μ p := hz.1
          calc F1k (n - 1) μ p = (F1k (n - 1) μ p ^ (1 / ((n : ℝ) - 1))) ^ ((n : ℝ) - 1) := by
                rw [← Real.rpow_mul hw0, one_div_mul_cancel hn1.ne', Real.rpow_one]
            _ ≤ (F1 μ p ^ (1 / (n : ℝ))) ^ ((n : ℝ) - 1) :=
                Real.rpow_le_rpow (Real.rpow_nonneg hw0 _) hL hn1.le
            _ = F1 μ p ^ (((n : ℝ) - 1) / (n : ℝ)) := by
                rw [← Real.rpow_mul hz0]; congr 1; ring
        have hpb := pointwise_bound_aff n hn2 r hr0 p hp
        obtain ⟨hgr, hval⟩ := hpb
        have hle := hgr.2 ⟨F1 μ p, hz, rfl⟩
        simp only at hle hval
        rw [hval] at hle
        have hnn : (0 : ℝ) ≤ n := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hFk hnn]
  refine ⟨part1, part2, ?_⟩
  -- Part 3: both minimax values equal `regret S Gn`
  have key : ∀ 𝓕 : Set (Measure (Fin n → ℝ)), Gn ∈ 𝓕 → 𝓕 ⊆ Fall n →
      (∀ μ ∈ 𝓕, regret S μ ≤ regret S Gn) → minimaxRegret n 𝓕 = regret S Gn := by
    intro 𝓕 hG𝓕 h𝓕 hp1
    unfold minimaxRegret
    have hbdd : ∀ m : {m : Mechanism n // m.IsDSIC},
        BddAbove (Set.range fun μ : 𝓕 => regret m.1 (μ : Measure (Fin n → ℝ))) := by
      intro m
      obtain ⟨C, hC⟩ := regret_bdd hn m.1 m.2
      exact ⟨C, by rintro _ ⟨μ, rfl⟩; exact hC μ (h𝓕 μ.2)⟩
    have hsup_ge : ∀ m : {m : Mechanism n // m.IsDSIC},
        regret S Gn ≤ ⨆ μ : 𝓕, regret m.1 (μ : Measure (Fin n → ℝ)) := fun m =>
      (part2 m.1 m.2).trans (le_ciSup (f := fun μ : 𝓕 => regret m.1 (μ : Measure (Fin n → ℝ)))
        (hbdd m) ⟨Gn, hG𝓕⟩)
    apply le_antisymm
    · refine (ciInf_le ⟨regret S Gn, ?_⟩ ⟨S, hS⟩).trans ?_
      · rintro _ ⟨m, rfl⟩; exact hsup_ge m
      · haveI : Nonempty 𝓕 := ⟨⟨Gn, hG𝓕⟩⟩
        exact ciSup_le fun μ => hp1 μ μ.2
    · haveI : Nonempty {m : Mechanism n // m.IsDSIC} := ⟨⟨S, hS⟩⟩
      exact le_ciInf hsup_ge
  rw [key (Faff n) hGn_aff (fun μ hμ => hμ.1.1) part1,
    key (Fiid n) hGn_iid (fun μ hμ => (Fiid_subset_Faff n hμ).1.1)
      (fun μ hμ => part1 μ (Fiid_subset_Faff n hμ))]
