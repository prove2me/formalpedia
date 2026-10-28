-- Prove2me | solution 1 for SinglePointPricing.Det.eq_4_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T08:50:32.124636+00:00
-- url     : https://prove2.me/submissions/02e649a6-e32d-42b3-871a-a2ec0301e2ef

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

section
namespace PriorPricingReduction
open SinglePointPricing.Det MeasureTheory Filter Topology

lemma hGA_pos (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) : 0 < GammaA α x := by
  unfold GammaA
  split_ifs with h
  · exact Real.exp_pos _
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply Real.rpow_pos_of_pos; nlinarith

lemma hGA_zero (α : ℝ) : GammaA α 0 = 1 := by
  unfold GammaA; split_ifs <;> simp

lemma hGAInv_one (α : ℝ) : GammaAInv α 1 = 0 := by
  unfold GammaAInv; split_ifs <;> simp

lemma hGAInv_GA (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    GammaAInv α (GammaA α x) = x := by
  unfold GammaA GammaAInv
  split_ifs with h
  · simp
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    have hb : 0 ≤ 1 + (1 - α) * x := by nlinarith
    rw [← Real.rpow_mul hb]
    have : -(1 / (1 - α)) * -(1 - α) = 1 := by field_simp
    rw [this, Real.rpow_one]; field_simp; ring

lemma hGA_GAInv (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : 0 < q) :
    GammaA α (GammaAInv α q) = q := by
  unfold GammaA GammaAInv
  split_ifs with h
  · simp [Real.exp_log hq]
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    have : 1 + (1 - α) * ((q ^ (-(1 - α)) - 1) / (1 - α)) = q ^ (-(1 - α)) := by
      field_simp; ring
    rw [this, ← Real.rpow_mul hq.le]
    have : -(1 - α) * -(1 / (1 - α)) = 1 := by field_simp
    rw [this, Real.rpow_one]

lemma hGAInv_pos (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    0 < GammaAInv α q := by
  rcases hq with ⟨h0, h1⟩
  unfold GammaAInv
  split_ifs with h
  · have := Real.log_neg h0 h1; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply div_pos _ ha
    have : 1 < q ^ (-(1 - α)) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (by linarith)
    linarith

/-- strict antitonicity of GammaAInv on (0, ∞) -/
lemma hGAInv_anti (α x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 < x) (hxy : x < y) :
    GammaAInv α y < GammaAInv α x := by
  unfold GammaAInv
  split_ifs with h
  · have := Real.log_lt_log hx hxy; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply div_lt_div_of_pos_right _ ha
    have := Real.rpow_lt_rpow_of_neg hx hxy (by linarith : -(1 - α) < 0)
    linarith

lemma hGA_anti (α x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) (hxy : x ≤ y) :
    GammaA α y ≤ GammaA α x := by
  unfold GammaA
  split_ifs with h
  · exact Real.exp_le_exp.mpr (by linarith)
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith)
    have : 0 < 1 / (1 - α) := by positivity
    linarith

lemma shape2 (α w q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ rSet α w q) :
    ∃ t s β : ℝ, 0 ≤ s ∧ s ≤ t ∧ 0 < β ∧ ∀ v, 0 ≤ v →
      Fbar α w q r v = if v ≤ t then GammaA α (β * max (v - s) 0) else 0 := by
  have hc := hGAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  by_cases hrw : r < w
  · have hr0 : 0 < r := by
      rcases hr with h | h
      · have : 0 < rLow α w q := by unfold rLow; positivity
        linarith [h.1]
      · linarith [h.1]
    refine ⟨w, r, c / (w - r), hr0.le, hrw.le, div_pos hc (by linarith), ?_⟩
    intro v hv
    simp only [Fbar, hrw, if_true, Gbar]
    by_cases hvr : v < r
    · rw [if_pos hvr, if_pos (by linarith), hGAInv_one, zero_mul, zero_div,
        max_eq_right (by linarith), mul_zero]
    · rw [if_neg hvr]
      by_cases hvw : v ≤ w
      · rw [if_pos hvw, if_pos hvw, div_one, one_mul, max_eq_left (by linarith)]
        congr 1; ring
      · rw [if_neg hvw, if_neg hvw]
  · push_neg at hrw
    refine ⟨r, 0, c / w, le_refl _, by linarith, div_pos hc hw, ?_⟩
    intro v hv
    simp only [Fbar, not_lt.mpr hrw, if_false, Gbar]
    rw [if_neg (by linarith)]
    by_cases hvr : v ≤ r
    · rw [if_pos hvr, if_pos hvr, div_one, one_mul, sub_zero, sub_zero, max_eq_left hv]
      congr 1; ring
    · rw [if_neg hvr, if_neg hvr]

lemma GAInv_nonneg (α u : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    0 ≤ GammaAInv α u := by
  rcases eq_or_lt_of_le hu1 with h | h
  · rw [h, hGAInv_one]
  · exact (hGAInv_pos α u hα ⟨hu0, h⟩).le

lemma GAInv_ge_iff (α u x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hu0 : 0 < u) (hx : 0 ≤ x) :
    x ≤ GammaAInv α u ↔ u ≤ GammaA α x := by
  have hG := hGA_pos α x hα hx
  constructor
  · intro h; by_contra hc; push_neg at hc
    have := hGAInv_anti α _ _ hα hG hc
    rw [hGAInv_GA α x hα hx] at this; linarith
  · intro h
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h', hGAInv_GA α x hα hx]
    · have := hGAInv_anti α _ _ hα hu0 h'
      rw [hGAInv_GA α x hα hx] at this; linarith

lemma vol_Ioo_inter_Iic (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    volume (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic g) = ENNReal.ofReal g := by
  apply le_antisymm
  · calc volume (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic g) ≤ volume (Set.Ioc 0 g) := by
          apply measure_mono; intro x hx; exact ⟨hx.1.1, hx.2⟩
      _ = ENNReal.ofReal g := by rw [Real.volume_Ioc, sub_zero]
  · calc ENNReal.ofReal g = volume (Set.Ioo 0 g) := by rw [Real.volume_Ioo, sub_zero]
      _ ≤ volume (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic g) := by
          apply measure_mono; intro x hx
          exact ⟨⟨hx.1, by linarith [hx.2]⟩, le_of_lt hx.2⟩

lemma construct (α t s β : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hs : 0 ≤ s) (hst : s ≤ t)
    (hβ : 0 < β) : ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Set.Iio 0) = 0 ∧
      ∀ v, 0 ≤ v → sf ν v = if v ≤ t then GammaA α (β * max (v - s) 0) else 0 := by
  set Q : ℝ → ℝ := fun u => min t (s + GammaAInv α u / β) with hQ
  have hmI : Measurable (fun u => GammaAInv α u) := by
    unfold GammaAInv; split_ifs <;> fun_prop
  have hQm : Measurable Q := by
    simp only [hQ]; fun_prop
  set lam0 : Measure ℝ := volume.restrict (Set.Ioo 0 1)
  haveI : IsProbabilityMeasure lam0 := ⟨by simp [lam0]⟩
  refine ⟨lam0.map Q, Measure.isProbabilityMeasure_map hQm.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_apply hQm measurableSet_Iio, Measure.restrict_apply (hQm measurableSet_Iio)]
    apply measure_mono_null _ (measure_empty (μ := volume))
    intro u ⟨hu1, hu2⟩
    exfalso
    have := GAInv_nonneg α u hα hu2.1 hu2.2.le
    simp only [Set.mem_preimage, Set.mem_Iio, hQ] at hu1
    have : 0 ≤ s + GammaAInv α u / β := by positivity
    have : 0 ≤ min t (s + GammaAInv α u / β) := le_min (by linarith) this
    linarith
  · intro v hv
    unfold sf
    rw [Measure.map_apply hQm measurableSet_Ici, Measure.restrict_apply (hQm measurableSet_Ici)]
    split_ifs with hvt
    · have hx : 0 ≤ β * max (v - s) 0 := mul_nonneg hβ.le (le_max_right _ _)
      have hg0 := hGA_pos α _ hα hx
      have hg1 : GammaA α (β * max (v - s) 0) ≤ 1 := by
        have := hGA_anti α 0 _ hα le_rfl hx; rwa [hGA_zero] at this
      have hset : Q ⁻¹' Set.Ici v ∩ Set.Ioo 0 1 =
          Set.Ioo (0 : ℝ) 1 ∩ Set.Iic (GammaA α (β * max (v - s) 0)) := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici, Set.mem_Ioo, Set.mem_Iic, hQ]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h2, ?_⟩
          rw [← GAInv_ge_iff α u _ hα h2.1 hx]
          have h3 : v ≤ s + GammaAInv α u / β := le_trans h1 (min_le_right _ _)
          have h4 := GAInv_nonneg α u hα h2.1 h2.2.le
          rcases le_total (v - s) 0 with h5 | h5
          · rw [max_eq_right h5, mul_zero]; exact h4
          · rw [max_eq_left h5]
            have : v - s ≤ GammaAInv α u / β := by linarith
            rwa [le_div_iff₀ hβ, mul_comm] at this
        · rintro ⟨h2, h1⟩
          refine ⟨?_, h2⟩
          rw [← GAInv_ge_iff α u _ hα h2.1 hx] at h1
          apply le_min hvt
          have : β * (v - s) ≤ GammaAInv α u := le_trans (by
            apply mul_le_mul_of_nonneg_left (le_max_left _ _) hβ.le) h1
          have : v - s ≤ GammaAInv α u / β := by rw [le_div_iff₀ hβ]; linarith
          linarith
      rw [hset, vol_Ioo_inter_Iic _ hg0.le hg1, ENNReal.toReal_ofReal hg0.le]
    · have hset : Q ⁻¹' Set.Ici v ∩ Set.Ioo 0 1 = ∅ := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici, hQ, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1 _
        have := le_trans h1 (min_le_left _ _)
        exact hvt this
      rw [hset, measure_empty, ENNReal.toReal_zero]

lemma sf_anti (μ : Measure ℝ) [IsFiniteMeasure μ] {x y : ℝ} (hxy : x ≤ y) : sf μ y ≤ sf μ x := by
  unfold sf
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Ici_subset_Ici.mpr hxy))

lemma sf_nn (μ : Measure ℝ) (x : ℝ) : 0 ≤ sf μ x := ENNReal.toReal_nonneg

lemma sf_left (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Tendsto (fun n : ℕ => sf μ (x - 1 / ((n : ℝ) + 1))) atTop (𝓝 (sf μ x)) := by
  have hanti : Antitone (fun n : ℕ => Set.Ici (x - 1 / ((n : ℝ) + 1))) := by
    intro n m hnm
    apply Set.Ici_subset_Ici.mpr
    have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.add_le_add_right hnm 1
    linarith
  have hI : (⋂ n : ℕ, Set.Ici (x - 1 / ((n : ℝ) + 1))) = Set.Ici x := by
    ext v; simp only [Set.mem_iInter, Set.mem_Ici]
    constructor
    · intro h
      by_contra hc; push_neg at hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hc)
      have := h n; linarith
    · intro h n; have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have := tendsto_measure_iInter_atTop (μ := μ) (fun n => measurableSet_Ici.nullMeasurableSet) hanti
    ⟨0, measure_ne_top μ _⟩
  rw [hI] at this
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp this

lemma usc_rev (μ : Measure ℝ) [IsFiniteMeasure μ] (N : ℝ) :
    UpperSemicontinuousOn (fun v => v * sf μ v) (Set.Icc 0 N) := by
  intro x hx y hy
  have h1 : Tendsto (fun n : ℕ => (x + 1 / ((n : ℝ) + 1)) * sf μ (x - 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (x * sf μ x)) := by
    have h2 : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (𝓝 x) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using this.const_add x
    exact h2.mul (sf_left μ x)
  obtain ⟨n, hn⟩ := (h1.eventually (gt_mem_nhds hy)).exists
  have hd : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hball : Set.Ioo (x - 1 / ((n : ℝ) + 1)) (x + 1 / ((n : ℝ) + 1)) ∈ 𝓝 x :=
    Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with x' hx' hx's
  have hs := sf_anti μ (le_of_lt hx'.1)
  have hnn := sf_nn μ (x - 1 / ((n : ℝ) + 1))
  calc x' * sf μ x' ≤ (x + 1 / ((n : ℝ) + 1)) * sf μ (x - 1 / ((n : ℝ) + 1)) := by
        apply mul_le_mul hx'.2.le hs (sf_nn μ x') (by linarith [hx's.1, hx'.1, hx'.2])
    _ < y := hn

lemma exists_opt (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Set.Iio 0) = 0)
    (hint : Integrable (fun v : ℝ => v) μ) (w0 : ℝ) (hw0' : 0 ≤ w0) (hw0 : 0 < w0 * sf μ w0) :
    ∃ r, 0 ≤ r ∧ ∀ v, 0 ≤ v → v * sf μ v ≤ r * sf μ r := by
  set m := w0 * sf μ w0
  have hanti : Antitone (fun n : ℕ => Set.Ici (n : ℝ)) := by
    intro n k hnk; exact Set.Ici_subset_Ici.mpr (by exact_mod_cast hnk)
  have hI : (⋂ n : ℕ, Set.Ici (n : ℝ)) = ∅ := by
    ext v; simp only [Set.mem_iInter, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
    intro h; obtain ⟨n, hn⟩ := exists_nat_gt v; have := h n; linarith
  have ht := tendsto_setIntegral_of_antitone (μ := μ) (f := fun v : ℝ => v)
    (fun n => measurableSet_Ici) hanti ⟨0, hint.integrableOn⟩
  rw [hI, Measure.restrict_empty, integral_zero_measure] at ht
  obtain ⟨N, hN⟩ := ((ht.eventually (gt_mem_nhds hw0)).and (eventually_ge_atTop ⌈w0⌉₊)).exists
  have hN0 : w0 ≤ (N : ℝ) := le_trans (Nat.le_ceil w0) (by exact_mod_cast hN.2)
  have htail : ∀ v, (N : ℝ) ≤ v → v * sf μ v < m := by
    intro v hv
    have hv0 : 0 ≤ v := le_trans (Nat.cast_nonneg N) hv
    have a1 : v * (μ (Set.Ici v)).toReal ≤ ∫ x in Set.Ici v, x ∂μ :=
      by
        have := setIntegral_ge_of_const_le (c := v) (μ := μ) (f := fun x : ℝ => x)
          measurableSet_Ici (measure_ne_top μ _) (fun x hx => hx) hint.integrableOn
        simpa [Measure.real, smul_eq_mul, mul_comm] using this
    have a2 : ∫ x in Set.Ici v, x ∂μ ≤ ∫ x in Set.Ici (N : ℝ), x ∂μ := by
      apply setIntegral_mono_set hint.integrableOn
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
        exact le_trans (Nat.cast_nonneg N) hx
      · exact Eventually.of_forall (fun x hx => le_trans hv hx)
    exact lt_of_le_of_lt (a1.trans a2) hN.1
  have hne : (Set.Icc (0 : ℝ) N).Nonempty := ⟨0, le_rfl, Nat.cast_nonneg N⟩
  obtain ⟨a, ha, hmax⟩ := (usc_rev μ (N : ℝ)).exists_isMaxOn hne isCompact_Icc
  refine ⟨a, ha.1, fun v hv => ?_⟩
  by_cases hvN : v ≤ N
  · exact hmax ⟨hv, hvN⟩
  · push_neg at hvN
    have := htail v hvN.le
    have := hmax (⟨hw0', hN0⟩ : w0 ∈ Set.Icc 0 (N : ℝ))
    simp only [Set.mem_setOf_eq] at this
    linarith

lemma interp_id (α qs qs' τ : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hqs : 0 < qs) (hqs' : 0 < qs')
    (hle : qs' ≤ qs) (hτ : 0 ≤ τ) :
    GammaAInv α (qs * GammaA α (GammaAInv α (qs' / qs) * τ)) =
      (1 - τ) * GammaAInv α qs + τ * GammaAInv α qs' := by
  have hk : 0 ≤ GammaAInv α (qs' / qs) := by
    rcases eq_or_lt_of_le hle with h | h
    · rw [h, div_self hqs.ne', hGAInv_one]
    · have := hGAInv_anti α (qs' / qs) 1 hα (div_pos hqs' hqs) ((div_lt_one hqs).mpr h)
      rw [hGAInv_one] at this; linarith
  unfold GammaA GammaAInv
  split_ifs with h
  · rw [Real.log_mul hqs.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_div hqs'.ne' hqs.ne']
    ring
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    set a := 1 - α with ha_def
    have hb : 0 ≤ 1 + a * ((qs' / qs) ^ (-a) - 1) / a * τ := by
      have h1 : 1 ≤ (qs' / qs) ^ (-a) := by
        apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos hqs' hqs)
          ((div_le_one hqs).mpr hle) (by linarith)
      have e : a * ((qs' / qs) ^ (-a) - 1) / a * τ = ((qs' / qs) ^ (-a) - 1) * τ := by
        field_simp
      rw [e]
      have : 0 ≤ ((qs' / qs) ^ (-a) - 1) * τ := mul_nonneg (by linarith) hτ
      linarith
    have hb' : 1 + a * (((qs' / qs) ^ (-a) - 1) / a * τ) = 1 + a * ((qs' / qs) ^ (-a) - 1) / a * τ := by ring
    rw [hb', Real.mul_rpow hqs.le (Real.rpow_nonneg hb _), ← Real.rpow_mul hb]
    have : -(1 / a) * -a = 1 := by field_simp
    rw [this, Real.rpow_one, Real.div_rpow hqs'.le hqs.le]
    have hp : 0 < qs ^ (-a) := Real.rpow_pos_of_pos hqs _
    field_simp
    ring

theorem lem1 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hSR : IsAlphaSR α μ) (s s' : ℝ) (hs : 0 ≤ s) (hss' : s ≤ s')
    (hq : 0 < sf μ s') :
    (∀ v ∈ Set.Icc s s',
      sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s)) ≤ sf μ v) ∧
    (∀ v ∈ Set.Ioi s',
      sf μ v ≤ sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s))) := by
  have hanti : ∀ x y, x ≤ y → sf μ y ≤ sf μ x := by
    intro x y hxy
    unfold sf
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Ici_subset_Ici.mpr hxy))
  have hnn : ∀ x, 0 ≤ sf μ x := fun x => ENNReal.toReal_nonneg
  have hqs : 0 < sf μ s := lt_of_lt_of_le hq (hanti _ _ hss')
  have hle : sf μ s' ≤ sf μ s := hanti _ _ hss'
  rcases eq_or_lt_of_le hss' with heq | hlt
  · subst heq
    simp only [sub_self, div_zero, hGA_zero, mul_one]
    refine ⟨?_, ?_⟩
    · intro v hv
      have : v = s := le_antisymm hv.2 hv.1
      rw [this]
    · intro v hv; exact hanti _ _ (le_of_lt hv)
  have hd : 0 < s' - s := sub_pos.mpr hlt
  set φ := fun v => GammaAInv α (sf μ v) with hφ
  have key : ∀ v, s ≤ v →
      GammaAInv α (sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s))) =
        (1 - (v - s) / (s' - s)) * φ s + (v - s) / (s' - s) * φ s' := by
    intro v hv
    rw [mul_div_assoc]
    exact interp_id α _ _ _ hα hqs hq hle (div_nonneg (by linarith) hd.le)
  have Ipos : ∀ v, s ≤ v →
      0 < sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s)) := by
    intro v hv
    have hk : 0 ≤ GammaAInv α (sf μ s' / sf μ s) := by
      rcases eq_or_lt_of_le hle with h | h
      · rw [h, div_self hqs.ne', hGAInv_one]
      · have := hGAInv_anti α _ 1 hα (div_pos hq hqs) ((div_lt_one hqs).mpr h)
        rw [hGAInv_one] at this; linarith
    exact mul_pos hqs (hGA_pos α _ hα (div_nonneg (mul_nonneg hk (by linarith)) hd.le))
  have hsD : s ∈ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} := ⟨hs, hqs⟩
  have hs'D : s' ∈ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} := ⟨by linarith, hq⟩
  refine ⟨?_, ?_⟩
  · intro v hv
    have hvpos : 0 < sf μ v := lt_of_lt_of_le hq (hanti _ _ hv.2)
    by_contra hcon
    push_neg at hcon
    have h1 := hGAInv_anti α _ _ hα hvpos hcon
    rw [key v hv.1] at h1
    -- convexity
    set τ := (v - s) / (s' - s) with hτ
    have hτ0 : 0 ≤ τ := div_nonneg (by linarith [hv.1]) hd.le
    have hτ1 : τ ≤ 1 := (div_le_one hd).mpr (by linarith [hv.2])
    have hc := hSR.2 hsD hs'D (sub_nonneg.mpr hτ1) hτ0 (by ring)
    have hv_eq : (1 - τ) • s + τ • s' = v := by
      simp only [smul_eq_mul]; rw [hτ]; field_simp; ring
    rw [hv_eq] at hc
    simp only [smul_eq_mul] at hc
    have : φ v = GammaAInv α (sf μ v) := rfl
    linarith
  · intro v hv
    have hv' : s' < v := hv
    rcases eq_or_lt_of_le (hnn v) with h0 | hvpos
    · rw [← h0]; exact (Ipos v (by linarith)).le
    by_contra hcon
    push_neg at hcon
    have h1 := hGAInv_anti α _ _ hα (Ipos v (by linarith)) hcon
    rw [key v (by linarith)] at h1
    have hvD : v ∈ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} := ⟨by linarith, hvpos⟩
    have hdv : 0 < v - s := by linarith
    set l := (s' - s) / (v - s) with hl
    have hl0 : 0 ≤ l := div_nonneg hd.le hdv.le
    have hl1 : l ≤ 1 := (div_le_one hdv).mpr (by linarith)
    have hc := hSR.2 hsD hvD (sub_nonneg.mpr hl1) hl0 (by ring)
    have hv_eq : (1 - l) • s + l • v = s' := by
      simp only [smul_eq_mul]; rw [hl]; field_simp; ring
    rw [hv_eq] at hc
    simp only [smul_eq_mul] at hc
    -- hc : φ s' ≤ (1 - l) * φ s + l * φ v
    have hlpos : 0 < l := div_pos hd hdv
    have hτl : (v - s) / (s' - s) * l = 1 := by rw [hl]; field_simp
    have : φ v = GammaAInv α (sf μ v) := rfl
    have hfin : (1 - (v - s) / (s' - s)) * φ s + (v - s) / (s' - s) * φ s' ≤ φ v := by
      have hτ0 : 0 ≤ (v - s) / (s' - s) := div_nonneg hdv.le hd.le
      have := mul_le_mul_of_nonneg_left hc hτ0
      have e : (v - s) / (s' - s) * ((1 - l) * φ s + l * φ v)
          = (v - s) / (s' - s) * φ s - φ s + φ v := by
        linear_combination (φ v - φ s) * hτl
      linarith
    linarith

lemma lemA (α β r v : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hr : 0 < r) (hβ : 1 ≤ β * r)
    (hv : r ≤ v) : v * GammaA α (β * (v - r)) ≤ r := by
  have hβ0 : 0 < β := by
    by_contra h; push_neg at h; nlinarith
  unfold GammaA
  split_ifs with h
  · have h1 := Real.add_one_le_exp (β * (v - r))
    have h2 : v ≤ r * Real.exp (β * (v - r)) := by nlinarith
    have he : Real.exp (-(β * (v - r))) = (Real.exp (β * (v - r)))⁻¹ := Real.exp_neg _
    rw [he]
    have hp := Real.exp_pos (β * (v - r))
    rw [← div_eq_mul_inv, div_le_iff₀ hp]; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    set a := 1 - α with ha_def
    have ha1 : a ≤ 1 := by rcases hα with ⟨h0, _⟩; linarith
    set B := 1 + a * (β * (v - r)) with hB
    have hB1 : 1 ≤ B := by have : 0 ≤ a * (β * (v - r)) := by
                              apply mul_nonneg ha.le; apply mul_nonneg hβ0.le; linarith
                           linarith
    have hBp : 0 < B := by linarith
    -- Bernoulli
    have hbern := rpow_one_add_le_one_add_mul_self (s := (v - r) / r)
      (by have : 0 ≤ (v - r) / r := div_nonneg (by linarith) hr.le
          linarith) ha.le ha1
    have e1 : 1 + (v - r) / r = v / r := by field_simp; ring
    rw [e1] at hbern
    have h2 : a * ((v - r) / r) ≤ a * (β * (v - r)) := by
      apply mul_le_mul_of_nonneg_left _ ha.le
      rw [div_le_iff₀ hr]; nlinarith
    have h3 : (v / r) ^ a ≤ B := by linarith
    have hvr : 0 ≤ v / r := div_nonneg (by linarith) hr.le
    have h4 : v / r ≤ B ^ (1 / a) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hvr a) h3 (by positivity : (0:ℝ) ≤ 1 / a)
      rwa [← Real.rpow_mul hvr, mul_one_div_cancel ha.ne', Real.rpow_one] at this
    rw [Real.rpow_neg hBp.le]
    have hp : 0 < B ^ (1 / a) := Real.rpow_pos_of_pos hBp _
    rw [← div_eq_mul_inv, div_le_iff₀ hp]
    rw [div_le_iff₀ hr] at h4; linarith

lemma lemB (α β r v : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : 0 ≤ β) (hαβ : α * β * r ≤ 1)
    (hv0 : 0 ≤ v) (hvr : v ≤ r) : v * GammaA α (β * v) ≤ r * GammaA α (β * r) := by
  rcases eq_or_lt_of_le hv0 with hv | hv
  · rw [← hv, zero_mul]
    exact mul_nonneg (by linarith) (hGA_pos α _ hα (by nlinarith)).le
  have hr : 0 < r := by linarith
  unfold GammaA
  split_ifs with h
  · subst h
    have hlog : β * (r - v) ≤ Real.log (r / v) := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hr hv)
      rw [inv_div] at this
      have e : 1 - v / r = (r - v) / r := by field_simp
      rw [e] at this
      have : β * (r - v) ≤ (r - v) / r := by
        rw [le_div_iff₀ hr]; nlinarith
      linarith
    have hexp : Real.exp (β * (r - v)) ≤ r / v := by
      calc Real.exp (β * (r - v)) ≤ Real.exp (Real.log (r / v)) := Real.exp_le_exp.mpr hlog
        _ = r / v := Real.exp_log (div_pos hr hv)
    have e : Real.exp (-(β * v)) = Real.exp (-(β * r)) * Real.exp (β * (r - v)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have hp := Real.exp_pos (-(β * r))
    rw [le_div_iff₀ hv] at hexp
    nlinarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    have hα0 : 0 ≤ α := hα.1
    set a := 1 - α with ha_def
    have ha1 : a ≤ 1 := by linarith
    have hαa : α = 1 - a := by linarith
    set x := r / v with hx
    have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hv]; linarith
    have hxpos : 0 < x := by linarith
    set X := x ^ a with hX
    have hXpos : 0 < X := Real.rpow_pos_of_pos hxpos _
    -- Bernoulli on (1/x)^a
    have hbern := rpow_one_add_le_one_add_mul_self (s := 1 / x - 1)
      (by have : 0 < 1 / x := by positivity
          linarith) ha.le ha1
    have e1 : 1 + (1 / x - 1) = x⁻¹ := by ring
    rw [e1, Real.inv_rpow hxpos.le, ← hX] at hbern
    -- hbern : X⁻¹ ≤ 1 + a * (1/x - 1)
    have hX2 : x ≤ X * (α * x + a) := by
      have : X⁻¹ * x ≤ (1 + a * (1 / x - 1)) * x := mul_le_mul_of_nonneg_right hbern hxpos.le
      have e2 : (1 + a * (1 / x - 1)) * x = α * x + a := by
        rw [hαa]; field_simp; ring
      rw [e2] at this
      have e3 : X⁻¹ * x * X = x := by field_simp
      have := mul_le_mul_of_nonneg_right this hXpos.le
      rw [e3] at this; linarith
    set Bv := 1 + a * (β * v) with hBv
    set Br := 1 + a * (β * r) with hBr
    have hBv1 : 1 ≤ Bv := by have : 0 ≤ a * (β * v) := by positivity
                             linarith
    have hBvp : 0 < Bv := by linarith
    have hBrp : 0 < Br := by have : 0 ≤ a * (β * r) := by positivity
                             linarith
    have hrx : r = x * v := by rw [hx]; field_simp
    -- Br * (α x + a) ≤ x * Bv
    have hk : Br * (α * x + a) ≤ x * Bv := by
      have hy : α * (β * v) * x ≤ 1 := by
        have : α * (β * v) * x = α * β * r := by rw [hrx]; ring
        linarith
      have : (x - 1) * (α * (β * v) * x - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      rw [hBr, hBv, hrx, hαa]
      rw [hαa] at this
      nlinarith
    have hpos2 : 0 < α * x + a := by positivity
    have hk2 : Br ≤ X * Bv := by
      have : Br * (α * x + a) ≤ X * Bv * (α * x + a) := by
        calc Br * (α * x + a) ≤ x * Bv := hk
          _ ≤ X * (α * x + a) * Bv := mul_le_mul_of_nonneg_right hX2 hBvp.le
          _ = X * Bv * (α * x + a) := by ring
      exact le_of_mul_le_mul_right this hpos2
    have hk3 : Br ^ (1 / a) ≤ x * Bv ^ (1 / a) := by
      have := Real.rpow_le_rpow hBrp.le hk2 (by positivity : (0:ℝ) ≤ 1 / a)
      rwa [Real.mul_rpow hXpos.le hBvp.le, hX, ← Real.rpow_mul hxpos.le,
        mul_one_div_cancel ha.ne', Real.rpow_one] at this
    rw [Real.rpow_neg hBvp.le, Real.rpow_neg hBrp.le]
    have p1 : 0 < Bv ^ (1 / a) := Real.rpow_pos_of_pos hBvp _
    have p2 : 0 < Br ^ (1 / a) := Real.rpow_pos_of_pos hBrp _
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ p1 p2]
    rw [hrx]
    nlinarith

theorem lemC2 (α w q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ rSet α w q) :
    r ∈ Set.Ici (0 : ℝ) ∧ IsMaxOn (fun v => v * Fbar α w q r v) (Set.Ici 0) r := by
  have hc := hGAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  by_cases hrw : r < w
  · have hrL : rLow α w q ≤ r := by
      rcases hr with h | h
      · exact h.1
      · linarith [h.1]
    have hrL' : w / (c + 1) ≤ r := hrL
    have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hrL'
    refine ⟨hr0.le, ?_⟩
    intro v hv
    simp only [Set.mem_setOf_eq]
    have hfr : r * Fbar α w q r r = r := by
      simp only [Fbar, hrw, if_true, Gbar, lt_irrefl, if_false, hrw.le, sub_self, mul_zero,
        zero_div, hGA_zero, mul_one]
    rw [hfr]
    simp only [Fbar, hrw, if_true, Gbar, div_one, one_mul]
    by_cases hvr : v < r
    · rw [if_pos hvr, hGAInv_one, zero_mul, zero_div, hGA_zero, mul_one]; exact hvr.le
    rw [if_neg hvr]
    by_cases hvw : v ≤ w
    · rw [if_pos hvw]
      have e : c * (v - r) / (w - r) = c / (w - r) * (v - r) := by ring
      rw [e]
      apply lemA α _ r v hα hr0 _ (not_lt.mp hvr)
      have hd : 0 < w - r := by linarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]
      rw [div_le_iff₀ (by linarith : (0:ℝ) < c + 1)] at hrL'
      linarith
    · rw [if_neg hvw]; simp [hr0.le]
  · push_neg at hrw
    have hr0 : 0 ≤ r := by linarith
    have hαcr : α * c * r ≤ w := by
      rcases hr with h | h
      · linarith [h.2]
      · exact h.2
    have hF1 : ∀ v, 0 ≤ v → v ≤ r → Fbar α w q r v = GammaA α (c * v / w) := by
      intro v hv0 hvr
      simp only [Fbar, not_lt.mpr hrw, if_false, Gbar]
      rw [if_neg (by linarith), if_pos hvr, div_one, one_mul, sub_zero, sub_zero]
    have hF2 : ∀ v, r < v → Fbar α w q r v = 0 := by
      intro v hv
      simp only [Fbar, not_lt.mpr hrw, if_false, Gbar]
      rw [if_neg (by linarith), if_neg (by linarith)]
    refine ⟨hr0, ?_⟩
    intro v hv
    have hv0 : 0 ≤ v := hv
    simp only [Set.mem_setOf_eq]
    rw [hF1 r hr0 le_rfl]
    have hgr : 0 ≤ r * GammaA α (c * r / w) :=
      mul_nonneg hr0 (hGA_pos α _ hα (by positivity)).le
    by_cases hvr : v ≤ r
    · rw [hF1 v hv0 hvr]
      have e1 : c * v / w = c / w * v := by ring
      have e2 : c * r / w = c / w * r := by ring
      rw [e1, e2]
      apply lemB α _ r v hα (by positivity) _ hv0 hvr
      have : α * (c / w) * r = α * c * r / w := by ring
      rw [this, div_le_one hw]; exact hαcr
    · rw [hF2 v ((not_le.mp hvr))]; simpa using hgr

lemma GA_ge (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) : 1 - x ≤ GammaA α x := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  unfold GammaA
  split_ifs with h
  · exact h1
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    have hb : 0 < 1 + (1 - α) * x := by nlinarith
    rw [Real.rpow_def_of_pos hb]
    refine le_trans h1 (Real.exp_le_exp.mpr ?_)
    have hl := Real.log_le_sub_one_of_pos hb
    have : Real.log (1 + (1 - α) * x) * (1 / (1 - α)) ≤ x := by
      rw [← div_eq_mul_one_div, div_le_iff₀ ha]; linarith
    have e : Real.log (1 + (1 - α) * x) * -(1 / (1 - α)) =
        -(Real.log (1 + (1 - α) * x) * (1 / (1 - α))) := by ring
    rw [e]; linarith

lemma GA_shift (α κ h : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hh : 0 ≤ h) (hhk : h ≤ κ) :
    GammaA α κ * (1 + h / (1 + (1 - α) * κ)) ≤ GammaA α (κ - h) := by
  unfold GammaA
  split_ifs with h1
  · subst h1
    simp only [sub_self, zero_mul, add_zero, div_one]
    have e : Real.exp (-(κ - h)) = Real.exp (-κ) * Real.exp h := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have := Real.add_one_le_exp h
    have hp := Real.exp_pos (-κ)
    nlinarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    set a := 1 - α with ha_def
    have hκ : 0 ≤ κ := le_trans hh hhk
    set A := 1 + a * κ with hA
    set B := 1 + a * (κ - h) with hB
    have hBp : 0 < B := by have : 0 ≤ a * (κ - h) := mul_nonneg ha.le (by linarith)
                           linarith
    have hAp : 0 < A := by have : 0 ≤ a * κ := mul_nonneg ha.le hκ
                           linarith
    have hAB : B ≤ A := by nlinarith
    -- (A/B)^(1/a) ≥ 1 + h/A
    have hp : 1 ≤ 1 / a := by rw [le_div_iff₀ ha]; linarith [hα.1]
    have hbern := one_add_mul_self_le_rpow_one_add (s := a * h / A)
      (by have : 0 ≤ a * h / A := by positivity
          linarith) hp
    have e1 : 1 / a * (a * h / A) = h / A := by field_simp
    rw [e1] at hbern
    have h2 : 1 + a * h / A ≤ A / B := by
      rw [le_div_iff₀ hBp]
      have : a * h / A * B = a * h * B / A := by ring
      have hdiv : a * h * B / A ≤ a * h := by
        rw [div_le_iff₀ hAp]; exact mul_le_mul_of_nonneg_left hAB (by positivity)
      nlinarith
    have h3 : (1 + a * h / A) ^ (1 / a) ≤ (A / B) ^ (1 / a) :=
      Real.rpow_le_rpow (by positivity) h2 (by positivity)
    rw [Real.div_rpow hAp.le hBp.le] at h3
    have hAr : 0 < A ^ (1 / a) := Real.rpow_pos_of_pos hAp _
    have hBr : 0 < B ^ (1 / a) := Real.rpow_pos_of_pos hBp _
    rw [Real.rpow_neg hAp.le, Real.rpow_neg hBp.le]
    have h4 : 1 + h / A ≤ A ^ (1 / a) / B ^ (1 / a) := le_trans hbern h3
    rw [le_div_iff₀ hBr] at h4
    rw [inv_mul_eq_div, div_le_iff₀ hAr, inv_mul_eq_div, le_div_iff₀ hBr]
    exact h4

lemma GA_ratio (α L K v r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hL : 0 ≤ L) (hLK : L ≤ K)
    (hv : 0 ≤ v) (hvr : v ≤ r) :
    GammaA α (L * v) * GammaA α (K * r) ≤ GammaA α (K * v) * GammaA α (L * r) := by
  unfold GammaA
  split_ifs with h1
  · rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    set a := 1 - α
    have hK : 0 ≤ K := le_trans hL hLK
    have hr : 0 ≤ r := le_trans hv hvr
    have p1 : 0 ≤ 1 + a * (L * v) := by positivity
    have p2 : 0 ≤ 1 + a * (K * r) := by positivity
    have p3 : 0 < 1 + a * (K * v) := by positivity
    have p4 : 0 < 1 + a * (L * r) := by positivity
    rw [← Real.mul_rpow p1 p2, ← Real.mul_rpow p3.le p4.le]
    apply Real.rpow_le_rpow_of_nonpos (mul_pos p3 p4)
    · have : 0 ≤ a * (K - L) * (r - v) := by
        apply mul_nonneg (mul_nonneg ha.le (by linarith)) (by linarith)
      nlinarith
    · have : 0 < 1 / a := by positivity
      linarith

lemma affine_convex (t k r : ℝ) : ConvexOn ℝ (Set.Icc 0 t) (fun v => k * (v - r)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x _ y _ a b _ _ hab
  simp only [smul_eq_mul]
  have : b = 1 - a := by linarith
  subst this; apply le_of_eq; ring

lemma shape (α w q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ rSet α w q) :
    ∃ t L, w ≤ t ∧ (∀ v, 0 ≤ v → v ≤ t → 0 < Fbar α w q r v ∧ GammaAInv α (Fbar α w q r v) = L v)
      ∧ (∀ v, t < v → Fbar α w q r v = 0) ∧ ConvexOn ℝ (Set.Icc 0 t) L ∧ Fbar α w q r w = q := by
  have hc := hGAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  by_cases hrw : r < w
  · have hr0 : 0 < r := by
      rcases hr with h | h
      · have : 0 < rLow α w q := by unfold rLow; positivity
        linarith [h.1]
      · linarith [h.1]
    refine ⟨w, fun v => max 0 (c / (w - r) * (v - r)), le_refl _, ?_, ?_, ?_, ?_⟩
    · intro v hv0 hvt
      simp only [Fbar, hrw, if_true, Gbar, hGAInv_one, zero_mul, zero_div, div_one, one_mul]
      by_cases hvr : v < r
      · simp only [hvr, if_true, hGA_zero, hGAInv_one]
        refine ⟨one_pos, ?_⟩
        have : c / (w - r) * (v - r) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (div_nonneg hc.le (by linarith)) (by linarith)
        rw [max_eq_left this]
      · simp only [hvr, if_false, hvt, if_true]
        have hx : 0 ≤ c * (v - r) / (w - r) :=
          div_nonneg (mul_nonneg hc.le (by linarith)) (by linarith)
        refine ⟨hGA_pos α _ hα hx, ?_⟩
        rw [hGAInv_GA α _ hα hx, max_eq_right (by rw [div_mul_eq_mul_div]; exact hx)]
        ring
    · intro v hv
      simp only [Fbar, hrw, if_true, Gbar]
      rw [if_neg (by linarith), if_neg (by linarith)]
    · exact (convexOn_const 0 (convex_Icc _ _)).sup (affine_convex w _ r)
    · simp only [Fbar, hrw, if_true, Gbar, div_one, one_mul]
      rw [if_neg (by linarith), if_pos le_rfl]
      rw [mul_div_assoc, div_self (by linarith), mul_one, hGA_GAInv α q hα hq.1]
  · push_neg at hrw
    refine ⟨r, fun v => c / w * (v - 0), hrw, ?_, ?_, affine_convex r _ 0, ?_⟩
    · intro v hv0 hvt
      simp only [Fbar, not_lt.mpr hrw, if_false, Gbar, div_one, one_mul, sub_zero]
      rw [if_neg (by linarith), if_pos hvt]
      have hx : 0 ≤ c * v / w := by positivity
      refine ⟨hGA_pos α _ hα hx, ?_⟩
      rw [hGAInv_GA α _ hα hx]; ring
    · intro v hv
      simp only [Fbar, not_lt.mpr hrw, if_false, Gbar]
      rw [if_neg (by linarith), if_neg (by linarith)]
    · simp only [Fbar, not_lt.mpr hrw, if_false, Gbar, div_one, one_mul, sub_zero]
      rw [if_neg (by linarith), if_pos hrw]
      rw [mul_div_assoc, div_self hw.ne', mul_one, hGA_GAInv α q hα hq.1]

theorem sfam_sub (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    SFamily α w q ⊆ FClass α w q := by
  rintro μ ⟨hP, h0, r, hr, hsf⟩
  obtain ⟨t, L, hwt, hpos, hzero, hconv, hww⟩ := shape α w q r hα hw hq hr
  have hsfw : sf μ w = q := by rw [hsf w hw.le, hww]
  have hIci : ∀ v, t < v → μ (Set.Ici v) = 0 := by
    intro v hv
    have h1 : sf μ v = 0 := by rw [hsf v (by linarith), hzero v hv]
    unfold sf at h1
    rcases (ENNReal.toReal_eq_zero_iff _).mp h1 with h | h
    · exact h
    · exact absurd h (measure_ne_top μ _)
  have hIoi : μ (Set.Ioi t) = 0 := by
    have : Set.Ioi t = ⋃ n : ℕ, Set.Ici (t + 1 / ((n : ℝ) + 1)) := by
      ext v; simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
      constructor
      · intro hv
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hv)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    rw [this]
    exact measure_iUnion_null (fun n => hIci _ (by have : 0 < 1 / ((n : ℝ) + 1) := by positivity
                                                   linarith))
  have hbd : ∀ᵐ v ∂μ, ‖v‖ ≤ t := by
    rw [ae_iff]
    apply measure_mono_null _ (measure_union_null h0 hIoi)
    intro v hv
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at hv
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    by_contra hc; push_neg at hc
    rw [abs_of_nonneg hc.1] at hv; linarith
  have hint : Integrable (fun v : ℝ => v) μ :=
    Integrable.of_bound (by fun_prop) t hbd
  have hnn : 0 ≤ᵐ[μ] (fun v : ℝ => v) := by
    rw [Filter.EventuallyLE, ae_iff]
    apply measure_mono_null _ h0
    intro v hv; simpa using hv
  refine ⟨⟨hP, h0, hint, ?_⟩, ?_, hsfw⟩
  · have := mul_meas_ge_le_integral_of_nonneg hnn hint w
    have e : {x : ℝ | w ≤ x} = Set.Ici w := rfl
    rw [e] at this
    have : w * sf μ w ≤ ∫ v, v ∂μ := this
    rw [hsfw] at this
    nlinarith [hq.1]
  · have hS : {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} = Set.Icc 0 t := by
      ext v; simp only [Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        by_contra hc; push_neg at hc
        rw [hsf v h1, hzero v hc] at h2; exact lt_irrefl _ h2
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [hsf v h1]; exact (hpos v h1 h2).1⟩
    unfold IsAlphaSR
    rw [hS]
    refine hconv.congr ?_
    intro v hv
    show L v = GammaAInv α (sf μ v)
    rw [hsf v hv.1, (hpos v hv.1 hv.2).2]

lemma sf_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) : sf μ x ≤ 1 := by
  unfold sf
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma sf_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (h0 : μ (Set.Iio 0) = 0) : sf μ 0 = 1 := by
  unfold sf
  rw [← Set.compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, h0]; simp

lemma GAInv_anti_le (α x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 < x) (hxy : x ≤ y) :
    GammaAInv α y ≤ GammaAInv α x := by
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · exact (hGAInv_anti α x y hα hx h).le

lemma key_dom (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (μ : Measure ℝ) (hμ : μ ∈ FClass α w q) :
    ∃ ν ∈ SFamily α w q, ∃ Oμ Oν : ℝ, 0 < Oμ ∧ 0 < Oν ∧ opt μ = Oμ ∧ opt ν = Oν ∧
      IsProbabilityMeasure ν ∧
      (∀ v, 0 ≤ v → v * sf μ v ≤ Oμ) ∧ (∀ v, 0 ≤ v → v * sf ν v ≤ Oν) ∧
      (∀ v, 0 ≤ v → sf ν v * Oμ ≤ sf μ v * Oν) := by
  obtain ⟨⟨hP, h0, hint, _⟩, hSR, hsfw⟩ := hμ
  haveI := hP
  have hwq : 0 < w * sf μ w := by rw [hsfw]; exact mul_pos hw hq.1
  obtain ⟨r, hr0, hmax⟩ := exists_opt μ h0 hint w hw.le hwq
  set qs := sf μ r with hqs_def
  have hrq : w * q ≤ r * qs := hsfw ▸ hmax w hw.le
  have hrq' : 0 < r * qs := lt_of_lt_of_le (mul_pos hw hq.1) hrq
  have hq0 : 0 ≤ qs := sf_nn μ r
  have hqs_pos : 0 < qs := by
    by_contra hcon; push_neg at hcon
    have : qs = 0 := le_antisymm hcon hq0
    rw [this, mul_zero] at hrq'; exact lt_irrefl _ hrq'
  have hr_pos : 0 < r := by
    by_contra hcon; push_neg at hcon
    have : r = 0 := le_antisymm hcon hr0
    rw [this, zero_mul] at hrq'; exact lt_irrefl _ hrq'
  have hqs1 : qs ≤ 1 := sf_le_one μ r
  have hsf0 : sf μ 0 = 1 := sf_zero μ h0
  have hc := hGAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  have main : r ∈ rSet α w q ∧
      ∀ v, 0 ≤ v → Fbar α w q r v * (r * qs) ≤ sf μ v * (r * Fbar α w q r r) := by
    by_cases hrw : r < w
    · have hqq : q ≤ qs := by rw [← hsfw]; exact sf_anti μ hrw.le
      have hl1 := (lem1 α hα μ h0 hSR r w hr0 hrw.le (by rw [hsfw]; exact hq.1)).1
      rw [hsfw] at hl1
      set k := GammaAInv α (q / qs) with hk_def
      have hratio_pos : 0 < q / qs := div_pos hq.1 hqs_pos
      have hratio_le : q / qs ≤ 1 := (div_le_one hqs_pos).mpr hqq
      have hk0 : 0 ≤ k := GAInv_nonneg α _ hα hratio_pos hratio_le
      have hkc : k ≤ c := GAInv_anti_le α q (q / qs) hα hq.1 (le_div_self hq.1.le hqs_pos hqs1)
      have hd : 0 < w - r := by linarith
      have hE3 : w ≤ r * (c + 1) := by
        by_contra hlt; push_neg at hlt
        set β' := k / (w - r) with hβ'
        have hβ'0 : 0 ≤ β' := div_nonneg hk0 hd.le
        have hβr : β' * r < 1 := by
          rw [hβ', div_mul_eq_mul_div, div_lt_one hd]; nlinarith
        set δ := min (w - r) ((1 - β' * r) / (2 * (β' + 1))) with hδ
        have hδpos : 0 < δ := lt_min hd (div_pos (by linarith) (by positivity))
        have hδw : δ ≤ w - r := min_le_left _ _
        have hδ2 : δ ≤ (1 - β' * r) / (2 * (β' + 1)) := min_le_right _ _
        have hβδ : β' * δ < 1 - β' * r := by
          have h1 : β' * δ ≤ β' * ((1 - β' * r) / (2 * (β' + 1))) :=
            mul_le_mul_of_nonneg_left hδ2 hβ'0
          have h2 : β' * ((1 - β' * r) / (2 * (β' + 1))) < 1 - β' * r := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
          linarith
        have hv := hl1 (r + δ) ⟨by linarith, by linarith⟩
        have e : k * (r + δ - r) / (w - r) = β' * δ := by rw [hβ']; ring
        rw [e] at hv
        have hg := GA_ge α (β' * δ) hα (mul_nonneg hβ'0 hδpos.le)
        have hm := hmax (r + δ) (by linarith)
        have h3 : qs * (1 - β' * δ) ≤ sf μ (r + δ) :=
          le_trans (mul_le_mul_of_nonneg_left hg hqs_pos.le) hv
        have h4 : (r + δ) * (qs * (1 - β' * δ)) ≤ (r + δ) * sf μ (r + δ) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
        have h5 : r * qs < (r + δ) * (qs * (1 - β' * δ)) := by
          have : (r + δ) * (qs * (1 - β' * δ)) - r * qs = qs * δ * (1 - β' * r - β' * δ) := by ring
          have : 0 < qs * δ * (1 - β' * r - β' * δ) := by
            apply mul_pos (mul_pos hqs_pos hδpos); linarith
          linarith
        linarith
      refine ⟨Or.inl ⟨?_, hrw⟩, ?_⟩
      · show w / (c + 1) ≤ r
        rw [div_le_iff₀ (by linarith)]; linarith
      · have hFr : Fbar α w q r r = 1 := by
          simp only [Fbar, hrw, if_true, Gbar, lt_irrefl, if_false, hrw.le, sub_self, mul_zero,
            zero_div, hGA_zero, mul_one]
        rw [hFr, mul_one]
        intro v hv
        suffices h : Fbar α w q r v * qs ≤ sf μ v by nlinarith
        by_cases hvr : v ≤ r
        · have h1 : Fbar α w q r v ≤ 1 := by
            simp only [Fbar, hrw, if_true, Gbar]
            split_ifs
            · rw [hGAInv_one, zero_mul, zero_div, hGA_zero]
            · rw [one_mul]; exact le_trans (hGA_anti α 0 _ hα le_rfl
                (div_nonneg (mul_nonneg (GAInv_nonneg α _ hα (by simpa using hq.1)
                  (by simpa using hq.2.le)) (by linarith)) hd.le)) (by rw [hGA_zero])
            · exact zero_le_one
          have h2 := sf_anti μ hvr
          nlinarith
        · push_neg at hvr
          by_cases hvw : v ≤ w
          · have hF : Fbar α w q r v = GammaA α (c * (v - r) / (w - r)) := by
              simp only [Fbar, hrw, if_true, Gbar]
              rw [if_neg (by linarith), if_pos hvw, div_one, one_mul]
            rw [hF]
            have h1 := hl1 v ⟨hvr.le, hvw⟩
            have h2 : GammaA α (c * (v - r) / (w - r)) ≤ GammaA α (k * (v - r) / (w - r)) :=
              hGA_anti α _ _ hα (div_nonneg (mul_nonneg hk0 (by linarith)) hd.le)
                (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hkc (by linarith)) hd.le)
            nlinarith
          · push_neg at hvw
            have hF : Fbar α w q r v = 0 := by
              simp only [Fbar, hrw, if_true, Gbar]
              rw [if_neg (by linarith), if_neg (by linarith)]
            rw [hF, zero_mul]; exact sf_nn μ v
    · push_neg at hrw
      have hqq : qs ≤ q := by rw [← hsfw]; exact sf_anti μ hrw
      set κ := GammaAInv α qs with hκ_def
      have hκc : c ≤ κ := GAInv_anti_le α qs q hα hqs_pos hqq
      have hκ0 : 0 < κ := lt_of_lt_of_le hc hκc
      have hconv : c * r ≤ κ * w := by
        have hD0 : (0 : ℝ) ∈ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} := ⟨le_rfl, by rw [hsf0]; exact one_pos⟩
        have hDr : r ∈ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} := ⟨hr0, hqs_pos⟩
        have hb0 : 0 ≤ w / r := div_nonneg hw.le hr0
        have hb1 : w / r ≤ 1 := (div_le_one hr_pos).mpr hrw
        have := hSR.2 hD0 hDr (sub_nonneg.mpr hb1) hb0 (by ring)
        simp only [smul_eq_mul, mul_zero, zero_add] at this
        have e : w / r * r = w := by field_simp
        rw [e, hsfw, hsf0, hGAInv_one, mul_zero, zero_add] at this
        -- this : c ≤ w / r * κ
        rw [div_mul_eq_mul_div, le_div_iff₀ hr_pos] at this
        linarith
      have hl1 := (lem1 α hα μ h0 hSR 0 r le_rfl hr0 hqs_pos).1
      rw [hsf0] at hl1
      have hl1' : ∀ v ∈ Set.Icc 0 r, GammaA α (κ / r * v) ≤ sf μ v := by
        intro v hv
        have := hl1 v hv
        rw [div_one, one_mul, sub_zero, sub_zero] at this
        convert this using 2; ring
      have hE4 : α * c * r ≤ w := by
        by_contra hlt; push_neg at hlt
        have hακ : 1 < α * κ := by
          have : w < α * κ * w := by nlinarith [hα.1]
          nlinarith
        set h := (α * κ - 1) / 2 with hh
        have hh0 : 0 < h := by rw [hh]; linarith
        have hα1 : α ≤ 1 := hα.2
        have hhκ : h ≤ κ := by rw [hh]; nlinarith
        set δ := r * h / κ with hδ
        have hδ0 : 0 ≤ δ := by positivity
        have hδr : δ ≤ r := by
          rw [hδ, div_le_iff₀ hκ0]; nlinarith
        have hv := hl1' (r - δ) ⟨by linarith, by linarith⟩
        have e : κ / r * (r - δ) = κ - h := by rw [hδ]; field_simp; try ring
        rw [e] at hv
        have hs := GA_shift α κ h hα hh0.le hhκ
        rw [hκ_def, hGA_GAInv α qs hα hqs_pos, ← hκ_def] at hs
        set A := 1 + (1 - α) * κ with hA
        have hA0 : 0 < A := by have : 0 ≤ (1 - α) * κ := mul_nonneg (by linarith) hκ0.le
                               linarith
        have hm := hmax (r - δ) (by linarith)
        have h4 : (r - δ) * (qs * (1 + h / A)) ≤ (r - δ) * sf μ (r - δ) :=
          mul_le_mul_of_nonneg_left (le_trans hs hv) (by linarith)
        have h5 : r * qs < (r - δ) * (qs * (1 + h / A)) := by
          have hAκ : α * κ - 1 = κ - A := by rw [hA]; ring
          have e2 : (r - δ) * (qs * (1 + h / A)) - r * qs =
              qs * r * h * (α * κ - 1 - h) / (κ * A) := by
            rw [hAκ, hδ]; field_simp; ring
          have : 0 < qs * r * h * (α * κ - 1 - h) / (κ * A) := by
            apply div_pos _ (mul_pos hκ0 hA0)
            apply mul_pos (mul_pos (mul_pos hqs_pos hr_pos) hh0); rw [hh]; linarith
          linarith
        linarith
      refine ⟨Or.inr ⟨hrw, hE4⟩, ?_⟩
      have hF : ∀ v, 0 ≤ v → v ≤ r → Fbar α w q r v = GammaA α (c / w * v) := by
        intro v hv0 hvr
        simp only [Fbar, not_lt.mpr hrw, if_false, Gbar]
        rw [if_neg (by linarith), if_pos hvr, div_one, one_mul, sub_zero, sub_zero]
        congr 1; ring
      rw [hF r hr0 le_rfl]
      intro v hv
      by_cases hvr : v ≤ r
      · rw [hF v hv hvr]
        have hLK : c / w ≤ κ / r := by
          rw [div_le_div_iff₀ hw hr_pos]; linarith
        have hrat := GA_ratio α (c / w) (κ / r) v r hα (by positivity) hLK hv hvr
        have e : κ / r * r = κ := by field_simp
        rw [e, hκ_def, hGA_GAInv α qs hα hqs_pos] at hrat
        have h1 := hl1' v ⟨hv, hvr⟩
        have hG0 : 0 ≤ GammaA α (c / w * r) := (hGA_pos α _ hα (by positivity)).le
        have : GammaA α (κ / r * v) * GammaA α (c / w * r) ≤ sf μ v * GammaA α (c / w * r) :=
          mul_le_mul_of_nonneg_right h1 hG0
        nlinarith
      · push_neg at hvr
        have hF0 : Fbar α w q r v = 0 := by
          simp only [Fbar, not_lt.mpr hrw, if_false, Gbar]
          rw [if_neg (by linarith), if_neg (by linarith)]
        rw [hF0, zero_mul]
        exact mul_nonneg (sf_nn μ v) (mul_nonneg hr0 (hGA_pos α _ hα (by positivity)).le)
  obtain ⟨hrS, hPt⟩ := main
  obtain ⟨t, s, β, hs0, hst, hβ, hshape⟩ := shape2 α w q r hα hw hq hrS
  obtain ⟨ν, hνP, hν0, hνsf⟩ := construct α t s β hα hs0 hst hβ
  have hνF : ∀ v, 0 ≤ v → sf ν v = Fbar α w q r v := by
    intro v hv; rw [hνsf v hv, hshape v hv]
  have hC2 := (lemC2 α w q r hα hw hq hrS).2
  have hFw : Fbar α w q r w = q := by
    by_cases hrw : r < w
    · simp only [Fbar, hrw, if_true, Gbar, div_one, one_mul]
      rw [if_neg (by linarith), if_pos le_rfl, mul_div_assoc, div_self (by linarith), mul_one,
        hGA_GAInv α q hα hq.1]
    · push_neg at hrw
      simp only [Fbar, not_lt.mpr hrw, if_false, Gbar, div_one, one_mul, sub_zero]
      rw [if_neg (by linarith), if_pos hrw, mul_div_assoc, div_self hw.ne', mul_one,
        hGA_GAInv α q hα hq.1]
  have hFr_pos : 0 < Fbar α w q r r := by
    have := hPt w hw.le
    rw [hFw, hsfw] at this
    by_contra hneg; push_neg at hneg
    have h1 : q * (r * Fbar α w q r r) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hq.1.le (mul_nonpos_of_nonneg_of_nonpos hr0 hneg)
    have h2 : 0 < q * (r * qs) := mul_pos hq.1 hrq'
    linarith
  refine ⟨ν, ⟨hνP, hν0, r, hrS, hνF⟩, r * qs, r * Fbar α w q r r, hrq', mul_pos hr_pos hFr_pos,
    ?_, ?_, hνP, fun v hv => hmax v hv, ?_, ?_⟩
  · apply IsGreatest.csSup_eq
    refine ⟨⟨r, hr0, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩; exact hmax v hv
  · apply IsGreatest.csSup_eq
    refine ⟨⟨r, hr0, by simp only [hνF r hr0]⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    simp only [hνF v hv]; exact hC2 hv
  · intro v hv; rw [hνF v hv]; exact hC2 hv
  · intro v hv; rw [hνF v hv]; exact hPt v hv

lemma ae_nonneg_mech (Ψ : Measure ℝ) (hΨ : IsMech Ψ) : ∀ᵐ p ∂Ψ, 0 ≤ p := by
  rw [ae_iff]
  have : {a : ℝ | ¬0 ≤ a} = Set.Iio 0 := by ext a; simp
  rw [this]; exact hΨ.2

lemma integrable_rev (Ψ μ : Measure ℝ) [IsFiniteMeasure μ] (hΨ : IsMech Ψ) (O : ℝ)
    (hb : ∀ v, 0 ≤ v → v * sf μ v ≤ O) : Integrable (fun p => p * sf μ p) Ψ := by
  haveI := hΨ.1
  have hm : Measurable (fun p => sf μ p) := Antitone.measurable (fun x y h => sf_anti μ h)
  apply Integrable.of_bound (measurable_id.mul hm).aestronglyMeasurable O
  filter_upwards [ae_nonneg_mech Ψ hΨ] with p hp
  show ‖p * sf μ p‖ ≤ O
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (sf_nn μ p))]
  exact hb p hp

lemma ratio_nonneg (Ψ μ : Measure ℝ) (hΨ : IsMech Ψ) : 0 ≤ ratio Ψ μ := by
  unfold ratio
  apply div_nonneg
  · apply integral_nonneg_of_ae
    filter_upwards [ae_nonneg_mech Ψ hΨ] with p hp
    exact mul_nonneg hp (sf_nn μ p)
  · unfold opt
    apply Real.sSup_nonneg
    rintro _ ⟨v, hv, rfl⟩
    exact mul_nonneg hv (sf_nn μ v)

theorem solution (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) (hw : 0 < w) (q : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (P' : Set (Measure ℝ)) (hP' : ∀ Ψ ∈ P', IsMech Ψ) :
    maximin P' (FClass α w q) = maximin P' (SFamily α w q) := by
  unfold maximin
  congr 1
  apply Set.image_congr
  intro Ψ hΨP
  have hΨ := hP' Ψ hΨP
  have hsub : SFamily α w q ⊆ FClass α w q := sfam_sub α w q hα hw hq
  have hdom : ∀ μ ∈ FClass α w q, ∃ ν ∈ SFamily α w q, ratio Ψ ν ≤ ratio Ψ μ := by
    intro μ hμ
    obtain ⟨ν, hνS, Oμ, Oν, hOμ, hOν, hoμ, hoν, hνP, hbμ, hbν, hpt⟩ := key_dom α w q hα hw hq μ hμ
    haveI := hνP
    haveI : IsProbabilityMeasure μ := hμ.1.1
    refine ⟨ν, hνS, ?_⟩
    unfold ratio
    rw [hoμ, hoν, div_le_div_iff₀ hOν hOμ, ← integral_mul_const, ← integral_mul_const]
    apply integral_mono_ae ((integrable_rev Ψ ν hΨ Oν hbν).mul_const _)
      ((integrable_rev Ψ μ hΨ Oμ hbμ).mul_const _)
    filter_upwards [ae_nonneg_mech Ψ hΨ] with p hp
    have := mul_le_mul_of_nonneg_left (hpt p hp) hp
    linarith [this, show p * sf ν p * Oμ = p * (sf ν p * Oμ) by ring,
      show p * sf μ p * Oν = p * (sf μ p * Oν) by ring]
  have hbdd : ∀ 𝓕 : Set (Measure ℝ), BddBelow (ratio Ψ '' 𝓕) := by
    intro 𝓕; refine ⟨0, ?_⟩; rintro _ ⟨μ, _, rfl⟩; exact ratio_nonneg Ψ μ hΨ
  rcases (FClass α w q).eq_empty_or_nonempty with hE | hNE
  · have : SFamily α w q = ∅ := Set.subset_eq_empty hsub hE
    rw [hE, this]
  · obtain ⟨μ0, hμ0⟩ := hNE
    obtain ⟨ν0, hν0, _⟩ := hdom μ0 hμ0
    apply le_antisymm
    · have hne : (ratio Ψ '' SFamily α w q).Nonempty := ⟨ratio Ψ ν0, ν0, hν0, rfl⟩
      exact csInf_le_csInf (hbdd _) hne (Set.image_mono hsub)
    · have hne2 : (ratio Ψ '' FClass α w q).Nonempty := ⟨ratio Ψ μ0, μ0, hμ0, rfl⟩
      apply le_csInf hne2
      rintro _ ⟨μ, hμ, rfl⟩
      obtain ⟨ν, hνS, hle⟩ := hdom μ hμ
      exact le_trans (csInf_le (hbdd _) ⟨ν, hνS, rfl⟩) hle

end PriorPricingReduction
end

section
open SinglePointPricing.Det MeasureTheory

namespace Queelius.SinglePointPricing

lemma ratio_dirac (p : ℝ) (μ : Measure ℝ) :
    ratio (Measure.dirac p) μ = p * sf μ p / opt μ := by
  simp [ratio]

lemma opt_eq_optFun (μ : Measure ℝ) (H : ℝ → ℝ)
    (h : ∀ p : ℝ, 0 ≤ p → sf μ p = H p) : opt μ = optFun H := by
  unfold opt optFun
  congr 1
  apply Set.image_congr
  intro p hp
  rw [h p hp]

lemma maximin_Pd_eq (F : Set (Measure ℝ)) :
    maximin Pd F = sSup ((fun p : ℝ => sInf ((fun μ => p * sf μ p / opt μ) '' F)) '' Set.Ici 0) := by
  unfold maximin
  congr 1
  ext x
  constructor
  · rintro ⟨Ψ, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, by simp only [ratio_dirac]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Measure.dirac p, ⟨p, hp, rfl⟩, by simp only [ratio_dirac]⟩

lemma dirac_isMech (p : ℝ) (hp : 0 ≤ p) : IsMech (Measure.dirac p) := by
  refine ⟨inferInstance, ?_⟩
  simp [Measure.dirac_apply', hp.not_gt]

lemma exists_Fbar_law (α w q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ rSet α w q) :
    ∃ μ ∈ SFamily α w q, ∀ p : ℝ, 0 ≤ p → sf μ p = Fbar α w q r p := by
  obtain ⟨t, s, β, hs, hst, hβ, hshape⟩ := PriorPricingReduction.shape2 α w q r hα hw hq hr
  obtain ⟨μ, hprob, hpos, htail⟩ := PriorPricingReduction.construct α t s β hα hs hst hβ
  have ht : ∀ p : ℝ, 0 ≤ p → sf μ p = Fbar α w q r p := by
    intro p hp
    rw [htail p hp, hshape p hp]
  exact ⟨μ, ⟨hprob, hpos, r, hr, ht⟩, ht⟩

lemma ratio_set_eq (α w q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hp : 0 ≤ p) :
    ratio (Measure.dirac p) '' SFamily α w q =
      (fun r => p * Fbar α w q r p / optFun (Fbar α w q r)) '' rSet α w q := by
  ext y
  constructor
  · rintro ⟨μ, ⟨_, _, r, hr, htail⟩, rfl⟩
    exact ⟨r, hr, by rw [ratio_dirac, opt_eq_optFun μ _ htail, htail p hp]⟩
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨μ, hμ, htail⟩ := exists_Fbar_law α w q r hα hw hq hr
    exact ⟨μ, hμ, by rw [ratio_dirac, opt_eq_optFun μ _ htail, htail p hp]⟩

/-- Exact deterministic maximin parameterization before the three-regime split. -/
theorem deterministic_parameterization (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    maximin Pd (FClass α w q) =
      sSup ((fun p : ℝ => sInf ((fun r => p * Fbar α w q r p /
        optFun (Fbar α w q r)) '' rSet α w q)) '' Set.Ici 0) := by
  rw [PriorPricingReduction.solution α hα w hw q hq Pd (by
    rintro Ψ ⟨p, hp, rfl⟩
    exact dirac_isMech p hp)]
  unfold maximin
  congr 1
  ext y
  constructor
  · rintro ⟨Ψ, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, congrArg sInf (ratio_set_eq α w q p hα hw hq hp).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Measure.dirac p, ⟨p, hp, rfl⟩, congrArg sInf (ratio_set_eq α w q p hα hw hq hp)⟩

lemma Fbar_one_below (α w q r p : ℝ) (hrw : r < w) (hpr : p ≤ r) :
    Fbar α w q r p = 1 := by
  by_cases hpr' : p < r
  · simp [Fbar, hrw, Gbar, hpr', PriorPricingReduction.hGAInv_one, PriorPricingReduction.hGA_zero]
  · have he : p = r := le_antisymm hpr (le_of_not_gt hpr')
    subst p
    simp [Fbar, hrw, Gbar, hrw.le, PriorPricingReduction.hGA_zero]

lemma optFun_eq_r (α w q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ rSet α w q) (hrw : r < w) :
    optFun (Fbar α w q r) = r := by
  obtain ⟨hr0, hmax⟩ := PriorPricingReduction.lemC2 α w q r hα hw hq hr
  have hfr : r * Fbar α w q r r = r := by rw [Fbar_one_below α w q r r hrw le_rfl, mul_one]
  apply le_antisymm
  · apply csSup_le
    · exact ⟨r * Fbar α w q r r, r, hr0, rfl⟩
    · rintro _ ⟨p, hp, rfl⟩
      have h := hmax hp
      change p * Fbar α w q r p ≤ r * Fbar α w q r r at h
      simpa only [hfr] using h
  · calc
      r = r * Fbar α w q r r := hfr.symm
      _ ≤ optFun (Fbar α w q r) := by
        apply le_csSup
        · refine ⟨r * Fbar α w q r r, ?_⟩
          rintro _ ⟨p, hp, rfl⟩
          exact hmax hp
        · exact ⟨r, hr0, rfl⟩

lemma rLow_pos_lt (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    0 < rLow α w q ∧ rLow α w q < w := by
  have hc := PriorPricingReduction.hGAInv_pos α q hα hq
  constructor
  · unfold rLow; positivity
  · exact (div_lt_self hw (by linarith))

lemma rLow_mem (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) : rLow α w q ∈ rSet α w q := by
  exact Or.inl ⟨le_rfl, (rLow_pos_lt α w q hα hw hq).2⟩

lemma parameter_nonneg (α w q p r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hp : 0 ≤ p) (hr : r ∈ rSet α w q) :
    0 ≤ p * Fbar α w q r p / optFun (Fbar α w q r) := by
  obtain ⟨μ, hμ, htail⟩ := exists_Fbar_law α w q r hα hw hq hr
  have h := PriorPricingReduction.ratio_nonneg (Measure.dirac p) μ (dirac_isMech p hp)
  rwa [ratio_dirac, opt_eq_optFun μ _ htail, htail p hp] at h

lemma parameter_inf_nonneg (α w q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hp : 0 ≤ p) :
    0 ≤ sInf ((fun r => p * Fbar α w q r p / optFun (Fbar α w q r)) '' rSet α w q) := by
  apply le_csInf
  · exact ⟨_, rLow α w q, rLow_mem α w q hα hw hq, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact parameter_nonneg α w q p r hα hw hq hp hr

lemma parameter_inf_zero (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    sInf ((fun r => 0 * Fbar α w q r 0 / optFun (Fbar α w q r)) '' rSet α w q) = 0 := by
  apply le_antisymm
  · have hz : (0 : ℝ) ∈ (fun r => 0 * Fbar α w q r 0 / optFun (Fbar α w q r)) '' rSet α w q :=
      ⟨rLow α w q, rLow_mem α w q hα hw hq, by simp⟩
    exact csInf_le ⟨0, by rintro _ ⟨r, hr, rfl⟩; simp⟩ hz
  · exact parameter_inf_nonneg α w q 0 hα hw hq le_rfl

lemma parameter_inf_above (α w q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hp : w < p) :
    sInf ((fun r => p * Fbar α w q r p / optFun (Fbar α w q r)) '' rSet α w q) = 0 := by
  have hp0 := le_of_lt (lt_trans hw hp)
  apply le_antisymm
  · have hlow := rLow_pos_lt α w q hα hw hq
    have hz : Fbar α w q (rLow α w q) p = 0 := by
      simp [Fbar, hlow.2, Gbar, not_lt.mpr (by linarith : rLow α w q ≤ p), not_le.mpr hp]
    have hb : BddBelow ((fun r => p * Fbar α w q r p / optFun (Fbar α w q r)) '' rSet α w q) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      exact parameter_nonneg α w q p r hα hw hq hp0 hr
    apply csInf_le hb
    exact ⟨rLow α w q, rLow_mem α w q hα hw hq, by simp [hz]⟩
  · exact parameter_inf_nonneg α w q p hα hw hq hp0

/-- Prices above w contribute only zero, already attained at price zero. -/
theorem deterministic_restricted (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    maximin Pd (FClass α w q) =
      sSup ((fun p : ℝ => sInf ((fun r => p * Fbar α w q r p /
        optFun (Fbar α w q r)) '' rSet α w q)) '' Set.Icc 0 w) := by
  rw [deterministic_parameterization α w q hα hw hq]
  congr 1
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    by_cases hpw : p ≤ w
    · exact ⟨p, ⟨hp, hpw⟩, rfl⟩
    · refine ⟨0, ⟨le_rfl, hw.le⟩, ?_⟩
      dsimp only
      rw [parameter_inf_zero α w q hα hw hq, parameter_inf_above α w q p hα hw hq (lt_of_not_ge hpw)]
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp.1, rfl⟩

end Queelius.SinglePointPricing

end

section
namespace SinglePointPricingEndpoint

/-- The right endpoint value is the greatest lower bound, even though the endpoint is excluded. -/
theorem isGLB_div_image_Ico (a w p : ℝ) (ha : 0 < a) (haw : a < w) (hp : 0 ≤ p) :
    IsGLB ((fun r : ℝ => p / r) '' Set.Ico a w) (p / w) := by
  have hw : 0 < w := lt_trans ha haw
  constructor
  · rintro y ⟨r, hr, rfl⟩
    exact div_le_div_of_nonneg_left hp (lt_of_lt_of_le ha hr.1) hr.2.le
  · intro b hb
    by_contra hnot
    have hbw : p / w < b := lt_of_not_ge hnot
    have hb0 : 0 < b := lt_of_le_of_lt (div_nonneg hp hw.le) hbw
    have hpb : p / b < w := by
      apply (div_lt_iff₀ hb0).2
      have h := (div_lt_iff₀ hw).1 hbw
      nlinarith
    have hmax : max a (p / b) < w := max_lt haw hpb
    let r : ℝ := (max a (p / b) + w) / 2
    have har : a < r := by
      have := le_max_left a (p / b)
      dsimp [r]
      linarith
    have hpr : p / b < r := by
      have := le_max_right a (p / b)
      dsimp [r]
      linarith
    have hrw : r < w := by dsimp [r]; linarith
    have hr0 : 0 < r := lt_trans ha har
    have hratio : p / r < b := by
      apply (div_lt_iff₀ hr0).2
      have h := (div_lt_iff₀ hb0).1 hpr
      nlinarith
    have hbound : b ≤ p / r := hb ⟨r, ⟨har.le, hrw⟩, rfl⟩
    linarith

theorem sInf_div_image_Ico (a w p : ℝ) (ha : 0 < a) (haw : a < w) (hp : 0 ≤ p) :
    sInf ((fun r : ℝ => p / r) '' Set.Ico a w) = p / w := by
  apply (isGLB_div_image_Ico a w p ha haw hp).csInf_eq
  exact ⟨p / a, a, ⟨le_rfl, haw⟩, rfl⟩

/-- Replacing a nonempty set by its greatest lower bound preserves the infimum after adjoining
any bounded-below set, including an empty one. This asserts infimum equality, not set equality. -/
theorem sInf_union_eq_singleton_union (s c : Set ℝ) (x : ℝ) (hs : s.Nonempty)
    (hx : IsGLB s x) (hc : BddBelow c) :
    sInf (s ∪ c) = sInf ({x} ∪ c) := by
  have hbounds : lowerBounds (s ∪ c) = lowerBounds ({x} ∪ c) := by
    ext b
    constructor
    · intro hb z hz
      rcases hz with hz | hz
      · rcases hz with rfl
        exact hx.2 (fun y hy => hb (Or.inl hy))
      · exact hb (Or.inr hz)
    · intro hb z hz
      rcases hz with hz | hz
      · exact le_trans (hb (Or.inl rfl)) (hx.1 hz)
      · exact hb (Or.inr hz)
  have hne : (s ∪ c).Nonempty := hs.mono Set.subset_union_left
  have hbounded : BddBelow (s ∪ c) := by
    obtain ⟨b, hb⟩ := hc
    refine ⟨min x b, ?_⟩
    intro z hz
    rcases hz with hz | hz
    · exact le_trans (min_le_left x b) (hx.1 hz)
    · exact le_trans (min_le_right x b) (hb hz)
  have hglb : IsGLB ({x} ∪ c) (sInf (s ∪ c)) := by
    change IsGreatest (lowerBounds ({x} ∪ c)) (sInf (s ∪ c))
    rw [← hbounds]
    exact isGLB_csInf hne hbounded
  exact (hglb.csInf_eq ⟨x, Or.inl rfl⟩).symm

theorem sInf_union_eq_of_common_isGLB (s t c : Set ℝ) (x : ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty) (hxs : IsGLB s x) (hxt : IsGLB t x)
    (hc : BddBelow c) : sInf (s ∪ c) = sInf (t ∪ c) := by
  rw [sInf_union_eq_singleton_union s c x hs hxs hc,
    sInf_union_eq_singleton_union t c x ht hxt hc]

#print axioms isGLB_div_image_Ico
#print axioms sInf_div_image_Ico
#print axioms sInf_union_eq_singleton_union
#print axioms sInf_union_eq_of_common_isGLB

end SinglePointPricingEndpoint

namespace SinglePointPricingEndpointControls

/-- Zero price is allowed; the middle group then consists of zero. -/
theorem zero_price : sInf ((fun r : ℝ => (0 : ℝ) / r) '' Set.Ico 1 2) = 0 := by
  simpa using SinglePointPricingEndpoint.sInf_div_image_Ico 1 2 0
    (by norm_num) (by norm_num) (by norm_num)

/-- The excluded endpoint really is an infimum, not a minimum of the image. -/
theorem endpoint_not_attained :
    (1 / 2 : ℝ) ∉ ((fun r : ℝ => (1 : ℝ) / r) '' Set.Ico 1 2) := by
  rintro ⟨r, hr, heq⟩
  have hr0 : 0 < r := by linarith [hr.1]
  have hlt : (1 / 2 : ℝ) < 1 / r := by
    exact one_div_lt_one_div_of_lt hr0 hr.2
  linarith

/-- A negative numerator reverses monotonicity, so its right endpoint is not a lower bound. -/
theorem negative_price_endpoint_fails :
    ¬ IsGLB ((fun r : ℝ => (-1 : ℝ) / r) '' Set.Ico 1 2) (-1 / 2) := by
  intro h
  have hbound : (-1 / 2 : ℝ) ≤ -1 / 1 := h.1 ⟨1, by norm_num, rfl⟩
  norm_num at hbound

/-- The adjoining set may be empty without relying on the value of real sInf(empty). -/
theorem empty_adjoining_set :
    sInf (((fun r : ℝ => (1 : ℝ) / r) '' Set.Ico 1 2) ∪ ∅) = (1 / 2 : ℝ) := by
  simpa using SinglePointPricingEndpoint.sInf_div_image_Ico 1 2 1
    (by norm_num) (by norm_num) (by norm_num)

#print axioms zero_price
#print axioms endpoint_not_attained
#print axioms negative_price_endpoint_fails
#print axioms empty_adjoining_set

end SinglePointPricingEndpointControls

end

section
open SinglePointPricing.Det MeasureTheory

namespace Queelius.SinglePointPricing

lemma Fbar_at_w (α w q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hrw : r < w) : Fbar α w q r w = q := by
  simp only [Fbar, hrw, if_true, Gbar, not_lt.mpr hrw.le, if_false, le_refl, div_one,
    one_mul]
  rw [mul_div_cancel_right₀ _ (sub_ne_zero.mpr (ne_of_gt hrw))]
  exact PriorPricingReduction.hGA_GAInv α q hα hq.1

lemma boundary_low_below_one (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ y ∈ (fun r => w * Fbar α w q r w / r) '' Set.Ico (rLow α w q) w, y ≤ 1 := by
  have hlo := rLow_pos_lt α w q hα hw hq
  have hqw : w * q < w := by nlinarith [hq.2]
  let r := (max (rLow α w q) (w * q) + w) / 2
  have hm : max (rLow α w q) (w * q) < w := max_lt hlo.2 hqw
  have hrL : rLow α w q ≤ r := by dsimp [r]; linarith [le_max_left (rLow α w q) (w * q)]
  have hrq : w * q < r := by dsimp [r]; linarith [le_max_right (rLow α w q) (w * q)]
  have hrw : r < w := by dsimp [r]; linarith
  have hr0 : 0 < r := lt_of_lt_of_le hlo.1 hrL
  refine ⟨w * Fbar α w q r w / r, ⟨r, ⟨hrL, hrw⟩, rfl⟩, ?_⟩
  rw [Fbar_at_w α w q r hα hq hrw]
  exact (div_le_one hr0).2 hrq.le

lemma sInf_insert_of_member_le (s : Set ℝ) (a y : ℝ) (hy : y ∈ s) (hya : y ≤ a)
    (hb : BddBelow s) : sInf (insert a s) = sInf s := by
  apply le_antisymm
  · apply csInf_le_csInf
    · obtain ⟨b, hb⟩ := hb
      exact ⟨min a b, by rintro z (rfl | hz); exact min_le_left _ _; exact le_trans (min_le_right _ _) (hb hz)⟩
    · exact ⟨y, hy⟩
    · exact Set.subset_insert a s
  · apply le_csInf ⟨a, Set.mem_insert a s⟩
    intro z hz
    rcases hz with rfl | hz
    · exact le_trans (csInf_le hb hy) hya
    · exact csInf_le hb hz

/-- At p=w, the artificial middle singleton is redundant rather than an empty-set infimum. -/
theorem parameter_inf_at_w (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    sInf ((fun r => w * Fbar α w q r w / optFun (Fbar α w q r)) '' rSet α w q) =
      sInf (((fun r => w * Fbar α w q r w / r) '' Set.Ico (rLow α w q) w) ∪ {w / w} ∪
        ((fun r => w * Fbar α w q r w / optFun (Fbar α w q r)) ''
          {r | w ≤ r ∧ α * GammaAInv α q * r ≤ w})) := by
  let A := (fun r => w * Fbar α w q r w / r) '' Set.Ico (rLow α w q) w
  let C := (fun r => w * Fbar α w q r w / optFun (Fbar α w q r)) ''
    {r | w ≤ r ∧ α * GammaAInv α q * r ≤ w}
  have heq : (fun r => w * Fbar α w q r w / optFun (Fbar α w q r)) '' rSet α w q = A ∪ C := by
    rw [rSet, Set.image_union]
    congr 1
    apply Set.image_congr
    intro r hr
    rw [optFun_eq_r α w q r hα hw hq (Or.inl hr) hr.2]
  have hb : BddBelow (A ∪ C) := by
    rw [← heq]
    refine ⟨0, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact parameter_nonneg α w q w r hα hw hq hw.le hr
  obtain ⟨y, hy, hy1⟩ := boundary_low_below_one α w q hα hw hq
  have hx : A ∪ {w / w} ∪ C = insert 1 (A ∪ C) := by
    rw [div_self hw.ne']
    ext z
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto
  rw [heq]
  change sInf (A ∪ C) = sInf (A ∪ {w / w} ∪ C)
  rw [hx, sInf_insert_of_member_le (A ∪ C) 1 y (Or.inl hy) hy1 hb]

end Queelius.SinglePointPricing

end

section
open SinglePointPricing.Det MeasureTheory

namespace Queelius.SinglePointPricing

/-- For an interior price the parameter-value image is a union of three exact images.
Only the second image will subsequently be replaced at the infimum level. -/
lemma regime_value_image (α w q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hpw : p < w) :
    ((fun r : ℝ => p * Fbar α w q r p / optFun (Fbar α w q r)) '' rSet α w q) =
      ((fun r : ℝ => p * Fbar α w q r p / r) '' Set.Ico (rLow α w q) p) ∪
      ((fun r : ℝ => p / r) '' Set.Ico (max (rLow α w q) p) w) ∪
      ((fun r : ℝ => p * Fbar α w q r p / optFun (Fbar α w q r)) ''
        {r : ℝ | w ≤ r ∧ α * GammaAInv α q * r ≤ w}) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with hr | hr
    · by_cases hrp : r < p
      · left; left
        refine ⟨r, ⟨hr.1, hrp⟩, ?_⟩
        dsimp only
        rw [optFun_eq_r α w q r hα hw hq (Or.inl hr) hr.2]
      · left; right
        have hpr : p ≤ r := le_of_not_gt hrp
        refine ⟨r, ⟨max_le hr.1 hpr, hr.2⟩, ?_⟩
        dsimp only
        rw [optFun_eq_r α w q r hα hw hq (Or.inl hr) hr.2,
          Fbar_one_below α w q r p hr.2 hpr, mul_one]
    · right
      exact ⟨r, hr, rfl⟩
  · intro hy
    rcases hy with (hy | hy) | hy
    · rcases hy with ⟨r, hr, rfl⟩
      have hrw : r < w := lt_trans hr.2 hpw
      refine ⟨r, Or.inl ⟨hr.1, hrw⟩, ?_⟩
      dsimp only
      rw [optFun_eq_r α w q r hα hw hq (Or.inl ⟨hr.1, hrw⟩) hrw]
    · rcases hy with ⟨r, hr, rfl⟩
      have hrl : rLow α w q ≤ r := le_trans (le_max_left _ _) hr.1
      have hpr : p ≤ r := le_trans (le_max_right _ _) hr.1
      refine ⟨r, Or.inl ⟨hrl, hr.2⟩, ?_⟩
      dsimp only
      rw [optFun_eq_r α w q r hα hw hq (Or.inl ⟨hrl, hr.2⟩) hr.2,
        Fbar_one_below α w q r p hr.2 hpr, mul_one]
    · rcases hy with ⟨r, hr, rfl⟩
      exact ⟨r, Or.inr hr, rfl⟩

/-- The three-regime infimum identity at interior prices; empty lower or upper groups are allowed. -/
theorem interior_regime_infimum (α w q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hp : 0 ≤ p) (hpw : p < w) :
    sInf ((fun r : ℝ => p * Fbar α w q r p / optFun (Fbar α w q r)) '' rSet α w q) =
      sInf (((fun r : ℝ => p * Fbar α w q r p / r) '' Set.Ico (rLow α w q) p) ∪
        {p / w} ∪ ((fun r : ℝ => p * Fbar α w q r p / optFun (Fbar α w q r)) ''
          {r : ℝ | w ≤ r ∧ α * GammaAInv α q * r ≤ w})) := by
  let A : Set ℝ := (fun r : ℝ => p * Fbar α w q r p / r) '' Set.Ico (rLow α w q) p
  let B : Set ℝ := (fun r : ℝ => p / r) '' Set.Ico (max (rLow α w q) p) w
  let C : Set ℝ := (fun r : ℝ => p * Fbar α w q r p / optFun (Fbar α w q r)) ''
    {r : ℝ | w ≤ r ∧ α * GammaAInv α q * r ≤ w}
  have hc : 0 < GammaAInv α q := PriorPricingReduction.hGAInv_pos α q hα hq
  have hl0 : 0 < rLow α w q := by unfold rLow; positivity
  have hlw : rLow α w q < w := by
    unfold rLow
    apply (div_lt_iff₀ (by linarith : 0 < GammaAInv α q + 1)).2
    nlinarith [mul_pos hw hc]
  have hmax0 : 0 < max (rLow α w q) p := lt_of_lt_of_le hl0 (le_max_left _ _)
  have hmaxw : max (rLow α w q) p < w := max_lt hlw hpw
  have hBne : B.Nonempty := by
    exact ⟨p / max (rLow α w q) p, max (rLow α w q) p, ⟨le_rfl, hmaxw⟩, rfl⟩
  have hBglb : IsGLB B (p / w) :=
    SinglePointPricingEndpoint.isGLB_div_image_Ico (max (rLow α w q) p) w p hmax0 hmaxw hp
  have hfull : BddBelow ((fun r : ℝ => p * Fbar α w q r p /
      optFun (Fbar α w q r)) '' rSet α w q) := by
    rw [← ratio_set_eq α w q p hα hw hq hp]
    refine ⟨0, ?_⟩
    rintro y ⟨μ, _, rfl⟩
    exact PriorPricingReduction.ratio_nonneg (Measure.dirac p) μ (dirac_isMech p hp)
  have himage : ((fun r : ℝ => p * Fbar α w q r p /
      optFun (Fbar α w q r)) '' rSet α w q) = A ∪ B ∪ C :=
    regime_value_image α w q p hα hw hq hpw
  have hAC : BddBelow (A ∪ C) := hfull.mono (by
    rw [himage]
    intro y hy
    rcases hy with hy | hy
    · exact Or.inl (Or.inl hy)
    · exact Or.inr hy)
  have hreplace := SinglePointPricingEndpoint.sInf_union_eq_singleton_union B (A ∪ C)
    (p / w) hBne hBglb hAC
  rw [himage]
  change sInf (A ∪ B ∪ C) = sInf (A ∪ {p / w} ∪ C)
  have hleft : A ∪ B ∪ C = B ∪ (A ∪ C) := by ext y; simp only [Set.mem_union]; tauto
  have hright : A ∪ {p / w} ∪ C = {p / w} ∪ (A ∪ C) := by
    ext y; simp only [Set.mem_union]; tauto
  rw [hleft, hright]
  exact hreplace

#print axioms regime_value_image
#print axioms interior_regime_infimum

end Queelius.SinglePointPricing

end

open SinglePointPricing.Det

/-- Display (4.1), line (b), p. 21: the deterministic maximin ratio as a supremum over prices
`p ∈ [0, w]` of the smallest of three worst-case ratios,
`inf_{r ∈ [r̲_α(w,q), p)} p F̄_α(p|r,(w,q))/r`, `p/w`, and
`inf_{r ∈ [w, r̄_α(w,q)]} p F̄_α(p|r,(w,q))/opt(F_α(·|r,(w,q)))`; the minimum of the three is the
infimum of the union of the three value sets (an empty group contributes nothing). -/
theorem solution (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    maximin Pd (FClass α w q) =
      sSup ((fun p : ℝ =>
        sInf (((fun r => p * Fbar α w q r p / r) '' Set.Ico (rLow α w q) p) ∪ {p / w} ∪
          ((fun r => p * Fbar α w q r p / optFun (Fbar α w q r)) ''
            {r | w ≤ r ∧ α * GammaAInv α q * r ≤ w}))) '' Set.Icc 0 w) := by
  rw [Queelius.SinglePointPricing.deterministic_restricted α w q hα hw hq]
  congr 1
  apply Set.image_congr
  intro p hp
  rcases eq_or_lt_of_le hp.2 with h | h
  · subst p
    exact Queelius.SinglePointPricing.parameter_inf_at_w α w q hα hw hq
  · exact Queelius.SinglePointPricing.interior_regime_infimum α w q p hα hw hq hp.1 h


