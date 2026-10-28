-- Prove2me | solution 1 for SinglePointPricing.Det.sFamily_subset_fClass
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:44:35.555984+00:00
-- url     : https://prove2.me/submissions/8100af30-b5ae-46d5-949f-b7d225690f6d

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

open SinglePointPricing.Det MeasureTheory

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

theorem solution (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
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
