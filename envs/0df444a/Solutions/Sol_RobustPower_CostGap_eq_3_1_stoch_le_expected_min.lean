-- Prove2me | solution 1 for RobustPower.CostGap.eq_3_1_stoch_le_expected_min
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:20:07.470085+00:00
-- url     : https://prove2.me/submissions/9da81ee6-abd0-47a1-8cf6-85349e17ff64

import Mathlib
import Definitions.Def_RobustPower_CostGap_Problems

open MeasureTheory Matrix


namespace RobustPower.CostGap

instance g25_prob_Icc : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

lemma g25_lt_iInf_iff {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    t < (⨅ j, x j) ↔ ∀ j, t < x j := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · intro h j
    exact lt_of_lt_of_le h (ciInf_le (Finite.bddBelow_range _) j)
  · intro h
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := x)
    rw [← hi]; exact h i

lemma g25_expected_min_pi {n : ℕ} (hn : 0 < n) :
    ∫ x, (⨅ j, x j) ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)))
      = 1 / ((n : ℝ) + 1) := by
  set ν := Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) with hν
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hmeas : Measurable (fun x : Fin n → ℝ => ⨅ j, x j) :=
    Measurable.iInf (fun j => measurable_pi_apply j)
  have hae : ∀ᵐ x ∂ν, ∀ j, x j ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro j
    have hmp := measurePreserving_eval (μ := fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) j
    have h1 : ∀ᵐ y ∂(ν.map (Function.eval j)), y ∈ Set.Icc (0 : ℝ) 1 := by
      rw [hmp.map_eq]; exact ae_restrict_mem measurableSet_Icc
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable h1
  have hint : Integrable (fun x : Fin n → ℝ => ⨅ j, x j) ν := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    filter_upwards [hae] with x hx
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := x)
    rw [← hi, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hx i).1], (hx i).2⟩
  have hnn : 0 ≤ᵐ[ν] (fun x : Fin n → ℝ => ⨅ j, x j) := by
    filter_upwards [hae] with x hx
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := x)
    show 0 ≤ ⨅ j, x j
    rw [← hi]; exact (hx i).1
  rw [hint.integral_eq_integral_meas_lt hnn]
  have hset : ∀ t ∈ Set.Ioi (0 : ℝ), ν.real {a | t < ⨅ j, a j} = (max (1 - t) 0) ^ n := by
    intro t ht
    have : {a : Fin n → ℝ | t < ⨅ j, a j} = Set.univ.pi (fun _ => Set.Ioi t) := by
      ext a; simp [g25_lt_iInf_iff hn]
    rw [this, measureReal_def, hν, Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    congr 1
    rw [Measure.restrict_apply measurableSet_Ioi]
    have : Set.Ioi t ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc t 1 := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith [Set.mem_Ioi.mp ht], h3⟩
    rw [this, Real.volume_Ioc, ENNReal.toReal_ofReal']
  rw [setIntegral_congr_fun measurableSet_Ioi hset]
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (s := Set.Ioc 0 1) Set.Ioc_subset_Ioi_self]
  swap
  · intro x hx
    simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at hx
    have : max (1 - x) 0 = 0 := max_eq_right (by linarith [hx.2 hx.1])
    rw [this, zero_pow hn.ne']
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hc : ∫ x in (0:ℝ)..1, (max (1 - x) 0) ^ n = ∫ x in (0:ℝ)..1, (1 - x) ^ n := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp only
    rw [max_eq_left (by linarith [hx.2])]
  rw [hc, intervalIntegral.integral_comp_sub_left (fun x => x ^ n) (1 : ℝ)]
  simp [integral_pow]

theorem eq_3_2_core {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∫ ω, (⨅ j, d ω j) ∂μ = 1 / ((n : ℝ) + 1) := by
  have hmeas : Measurable (fun x : Fin n → ℝ => ⨅ j, x j) :=
    Measurable.iInf (fun j => measurable_pi_apply j)
  have := integral_map (μ := μ) hd.aemeasurable (hmeas.aestronglyMeasurable)
  rw [hlaw] at this
  rw [← g25_expected_min_pi hn, this]


lemma g25_d_mem {n : ℕ} {Ω : Type*} (d : Ω → Fin n → ℝ) (hrange : Set.range d = Set.Icc 0 1)
    (ω : Ω) (j : Fin n) : 0 ≤ d ω j ∧ d ω j ≤ 1 := by
  have h : d ω ∈ Set.Icc (0 : Fin n → ℝ) 1 := hrange ▸ Set.mem_range_self ω
  exact ⟨h.1 j, h.2 j⟩

theorem eq_3_1_core {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d) (hrange : Set.range d = Set.Icc 0 1) :
    zStochBD μ (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
        (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ ≤
      ((∫ ω, (⨅ j, d ω j) ∂μ : ℝ) : EReal) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set m : Ω → ℝ := fun ω => ⨅ j, d ω j with hm_def
  have hdj : ∀ j, Measurable (fun ω => d ω j) := fun j => (measurable_pi_apply j).comp hd
  have hm : Measurable m := Measurable.iInf hdj
  set ind : Ω → Fin n → ℝ := fun ω j => if d ω j = m ω then 1 else 0 with hind_def
  set N : Ω → ℝ := fun ω => ∑ k, ind ω k with hN_def
  have hind_meas : ∀ j, Measurable (fun ω => ind ω j) := by
    intro j
    exact Measurable.ite (measurableSet_eq_fun (hdj j) hm) measurable_const measurable_const
  have hN_meas : Measurable N := Finset.measurable_sum _ (fun k _ => hind_meas k)
  have hind_nn : ∀ ω j, 0 ≤ ind ω j := by intro ω j; simp only [hind_def]; split_ifs <;> norm_num
  have hind_le : ∀ ω j, ind ω j ≤ 1 := by intro ω j; simp only [hind_def]; split_ifs <;> norm_num
  have hN_ge : ∀ ω, 1 ≤ N ω := by
    intro ω
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := d ω)
    have h1 : ind ω i = 1 := by simp [hind_def, hm_def, hi]
    calc (1 : ℝ) = ind ω i := h1.symm
      _ ≤ N ω := Finset.single_le_sum (fun k _ => hind_nn ω k) (Finset.mem_univ i)
  have hN_pos : ∀ ω, 0 < N ω := fun ω => lt_of_lt_of_le one_pos (hN_ge ω)
  set y : Ω → Fin n → ℝ := fun ω j => ind ω j / N ω with hy_def
  have hy_nn : ∀ ω j, 0 ≤ y ω j := fun ω j => div_nonneg (hind_nn ω j) (hN_pos ω).le
  have hy_le : ∀ ω j, y ω j ≤ 1 := by
    intro ω j
    rw [hy_def, div_le_one (hN_pos ω)]
    exact le_trans (hind_le ω j) (hN_ge ω)
  have hy_sum : ∀ ω, ∑ j, y ω j = 1 := by
    intro ω
    simp only [hy_def]
    rw [← Finset.sum_div]
    exact div_self (hN_pos ω).ne'
  have hy_dot : ∀ ω, d ω ⬝ᵥ y ω = m ω := by
    intro ω
    simp only [dotProduct, hy_def]
    have : ∀ j, d ω j * (ind ω j / N ω) = m ω * (ind ω j / N ω) := by
      intro j
      by_cases h : d ω j = m ω
      · rw [h]
      · simp [hind_def, h]
    simp_rw [this]
    rw [← Finset.mul_sum, ← Finset.sum_div, div_self (hN_pos ω).ne', mul_one]
  have hy_meas : Measurable y := by
    apply measurable_pi_lambda
    intro j
    exact (hind_meas j).div hN_meas
  have hy_int : Integrable y μ := by
    refine Integrable.of_bound hy_meas.aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
    intro ω
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr ?_
    intro j
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hy_nn ω j], hy_le ω j⟩
  have hm_bd : ∀ ω, 0 ≤ m ω ∧ m ω ≤ 1 := by
    intro ω
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := d ω)
    have : m ω = d ω i := by simp [hm_def, hi]
    rw [this]; exact g25_d_mem d hrange ω i
  have hm_int : Integrable m μ := by
    refine Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
    intro ω
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hm_bd ω).1], (hm_bd ω).2⟩
  have hdot_eq : (fun ω => d ω ⬝ᵥ y ω) = m := funext hy_dot
  have hfeas : StochFeasibleBD μ (0 : Matrix (Fin 1) (Fin 0) ℝ)
      (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ) (fun _ _ => 1 : Ω → Fin 1 → ℝ) d ∅ ∅
      (0 : Fin 0 → ℝ) y := by
    refine ⟨⟨le_refl _, by simp⟩, hy_int, hdot_eq ▸ hm_int, ?_⟩
    intro ω
    refine ⟨⟨fun j => hy_nn ω j, by simp⟩, ?_⟩
    intro i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add, one_mul]
    rw [hy_sum ω]
  refine iInf_le_of_le (0 : Fin 0 → ℝ) (iInf_le_of_le y (iInf_le_of_le hfeas ?_))
  rw [hdot_eq]
  simp [hm_def]

theorem robust_ge_one_core {n : ℕ} (hn : 0 < n) {Ω : Type*}
    (d : Ω → Fin n → ℝ) (hrange : Set.range d = Set.Icc 0 1) :
    (1 : EReal) ≤
      zRobBD (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
          (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ := by
  have h1 : (1 : Fin n → ℝ) ∈ Set.range d := by
    rw [hrange]; exact ⟨zero_le_one, le_refl _⟩
  obtain ⟨ω₀, hω₀⟩ := h1
  refine le_iInf fun x => le_iInf fun y => le_iInf fun hf => ?_
  have hb := hf.2.2 ω₀ ⟨0, Nat.one_pos⟩
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add, one_mul] at hb
  have hdot : d ω₀ ⬝ᵥ y = ∑ j, y j := by
    rw [hω₀]; simp [dotProduct]
  calc (1 : EReal) = ((0 : Fin 0 → ℝ) ⬝ᵥ x : ℝ) + ((1 : ℝ) : EReal) := by simp
    _ ≤ ((0 : Fin 0 → ℝ) ⬝ᵥ x : ℝ) + ((d ω₀ ⬝ᵥ y : ℝ) : EReal) := by
        gcongr
        rw [hdot]; exact_mod_cast hb
    _ ≤ _ := by
        gcongr
        exact le_iSup (fun ω => ((d ω ⬝ᵥ y : ℝ) : EReal)) ω₀

theorem goal_core {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d) (hrange : Set.range d = Set.Icc 0 1)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    (((n : ℝ) + 1 : ℝ) : EReal) *
        zStochBD μ (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
          (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ ≤
      zRobBD (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
          (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ := by
  have hS := eq_3_1_core hn μ d hd hrange
  rw [eq_3_2_core hn μ d hd hlaw] at hS
  refine le_trans ?_ (robust_ge_one_core hn d hrange)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  generalize zStochBD μ (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
          (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ = z at hS ⊢
  induction z using EReal.rec with
  | bot => rw [EReal.mul_bot_of_pos (by exact_mod_cast hpos)]; exact bot_le
  | top => exact absurd hS (by simp)
  | coe r =>
    have hr : r ≤ 1 / ((n : ℝ) + 1) := by exact_mod_cast hS
    rw [← EReal.coe_mul]
    have : ((n : ℝ) + 1) * r ≤ 1 := by
      rw [le_div_iff₀ hpos] at hr; linarith
    exact_mod_cast this

end RobustPower.CostGap

open RobustPower.CostGap
open MeasureTheory Matrix

theorem solution {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d) (hrange : Set.range d = Set.Icc 0 1) :
    zStochBD μ (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
        (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ ≤
      ((∫ ω, (⨅ j, d ω j) ∂μ : ℝ) : EReal) := by
  exact eq_3_1_core hn μ d hd hrange
