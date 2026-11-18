-- Prove2me | solution 1 for OWMR.dfr_window_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T09:57:50.845903+00:00
-- url     : https://prove2.me/submissions/0da096ee-f1a8-4cf5-998e-e0f83b938a77

import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Theorems.Thm_OWMR_F_properties
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Slope

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace DFRQ

/-! ### The quantile function of `U` restricted to `[0, wh)` -/

variable (U : Measure ℝ) (wh : ℝ)

/-- CDF of `U` restricted to `[0, wh)`. -/
def Φ (x : ℝ) : ℝ := (U (Ico 0 wh ∩ Iic x)).toReal

/-- Total mass `M = U[0, wh)`. -/
def Mt : ℝ := (U (Ico 0 wh)).toReal

/-- The (left-continuous) quantile function on `[0, M]`. -/
def Q (v : ℝ) : ℝ := sInf {x | x ∈ Icc 0 wh ∧ min v (Mt U wh) ≤ Φ U wh x}

variable {U wh}

lemma Φ_mono (hfin : U (Ico 0 wh) ≠ ∞) : Monotone (Φ U wh) := fun a b hab =>
  ENNReal.toReal_mono (ne_top_of_le_ne_top hfin (measure_mono inter_subset_left))
    (measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.2 hab)))

lemma Φ_le (hfin : U (Ico 0 wh) ≠ ∞) (x : ℝ) : Φ U wh x ≤ Mt U wh :=
  ENNReal.toReal_mono hfin (measure_mono inter_subset_left)

lemma Φ_nonneg (x : ℝ) : 0 ≤ Φ U wh x := ENNReal.toReal_nonneg

lemma Φ_neg {x : ℝ} (hx : x < 0) : Φ U wh x = 0 := by
  unfold Φ
  have : Ico 0 wh ∩ Iic x = ∅ := by
    refine eq_empty_of_forall_notMem fun y hy => ?_
    simp only [mem_inter_iff, mem_Ico, mem_Iic] at hy
    linarith [hy.1.1, hy.2]
  rw [this, measure_empty, ENNReal.toReal_zero]

lemma Φ_top {x : ℝ} (hx : wh ≤ x) : Φ U wh x = Mt U wh := by
  unfold Φ Mt
  congr 2
  exact inter_eq_left.2 fun y hy => mem_Iic.2 (by simp only [mem_Ico] at hy; linarith [hy.2])

lemma Φ_eq_W {x : ℝ} (hx0 : 0 ≤ x) (hx : x < wh) : Φ U wh x = (U (Icc 0 x)).toReal := by
  unfold Φ
  congr 2
  ext y
  simp only [mem_inter_iff, mem_Ico, mem_Iic, mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩

/-- Right continuity of the CDF. -/
lemma Φ_rcont (hfin : U (Ico 0 wh) ≠ ∞) (x : ℝ) :
    Tendsto (fun n : ℕ => Φ U wh (x + 1 / (n + 1))) atTop (𝓝 (Φ U wh x)) := by
  have hanti : Antitone fun n : ℕ => Ico 0 wh ∩ Iic (x + 1 / ((n : ℝ) + 1)) := by
    intro a b hab
    refine inter_subset_inter_right _ (Iic_subset_Iic.2 ?_)
    have : (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    linarith
  have hinter : ⋂ n : ℕ, Ico 0 wh ∩ Iic (x + 1 / ((n : ℝ) + 1)) = Ico 0 wh ∩ Iic x := by
    ext y
    simp only [mem_iInter, mem_inter_iff, mem_Iic]
    constructor
    · intro h
      refine ⟨(h 0).1, ?_⟩
      have ht : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (𝓝 x) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add x
      exact ge_of_tendsto' ht fun n => (h n).2
    · rintro ⟨h1, h2⟩ n
      exact ⟨h1, by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                    linarith⟩
  have h := tendsto_measure_iInter_atTop (μ := U)
    (fun n => (measurableSet_Ico.inter measurableSet_Iic).nullMeasurableSet) hanti
    ⟨0, ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)⟩
  rw [hinter] at h
  exact (ENNReal.tendsto_toReal (ne_top_of_le_ne_top hfin (measure_mono inter_subset_left))).comp h

lemma Q_mem (hwh : 0 ≤ wh) (hfin : U (Ico 0 wh) ≠ ∞) (v : ℝ) :
    wh ∈ {x | x ∈ Icc 0 wh ∧ min v (Mt U wh) ≤ Φ U wh x} :=
  ⟨⟨hwh, le_rfl⟩, by rw [Φ_top le_rfl]; exact min_le_right _ _⟩

lemma Q_bdd (v : ℝ) : BddBelow {x | x ∈ Icc 0 wh ∧ min v (Mt U wh) ≤ Φ U wh x} :=
  ⟨0, fun x hx => hx.1.1⟩

lemma Q_nonneg (hwh : 0 ≤ wh) (hfin : U (Ico 0 wh) ≠ ∞) (v : ℝ) : 0 ≤ Q U wh v :=
  le_csInf ⟨wh, Q_mem hwh hfin v⟩ fun x hx => hx.1.1

lemma Q_le (hwh : 0 ≤ wh) (hfin : U (Ico 0 wh) ≠ ∞) (v : ℝ) : Q U wh v ≤ wh :=
  csInf_le (Q_bdd v) (Q_mem hwh hfin v)

lemma Q_mono (hwh : 0 ≤ wh) (hfin : U (Ico 0 wh) ≠ ∞) : Monotone (Q U wh) := by
  intro a b hab
  refine csInf_le_csInf (Q_bdd a) ⟨wh, Q_mem hwh hfin b⟩ fun x hx => ⟨hx.1, ?_⟩
  exact le_trans (min_le_min_right _ hab) hx.2

/-- The infimum is attained: `v ≤ Φ(Q v)` for `v ≤ M`. -/
lemma Φ_Q (hwh : 0 ≤ wh) (hfin : U (Ico 0 wh) ≠ ∞) {v : ℝ} (hvM : v ≤ Mt U wh) :
    v ≤ Φ U wh (Q U wh v) := by
  have hne : ({x | x ∈ Icc 0 wh ∧ min v (Mt U wh) ≤ Φ U wh x} : Set ℝ).Nonempty :=
    ⟨wh, Q_mem hwh hfin v⟩
  have hev : ∀ n : ℕ, v ≤ Φ U wh (Q U wh v + 1 / (n + 1)) := by
    intro n
    have hlt : Q U wh v < Q U wh v + 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt hne hlt
    have := hy.2
    rw [min_eq_left hvM] at this
    exact le_trans this (Φ_mono hfin hylt.le)
  exact ge_of_tendsto' (Φ_rcont hfin _) hev

/-- Galois connection on `[0, wh]`. -/
lemma Q_le_iff (hwh : 0 ≤ wh) (hfin : U (Ico 0 wh) ≠ ∞) {v : ℝ} (hvM : v ≤ Mt U wh)
    {x : ℝ} (hx : x ∈ Icc 0 wh) : Q U wh v ≤ x ↔ v ≤ Φ U wh x := by
  constructor
  · intro h
    exact le_trans (Φ_Q hwh hfin hvM) (Φ_mono hfin h)
  · intro h
    refine csInf_le (Q_bdd v) ⟨hx, ?_⟩
    rw [min_eq_left hvM]
    exact h

lemma Q_meas (hwh : 0 ≤ wh) (hfin : U (Ico 0 wh) ≠ ∞) : Measurable (Q U wh) :=
  (Q_mono hwh hfin).measurable

lemma vol_Ioo_inter (Mw c : ℝ) (hMw : 0 ≤ Mw) (hc : 0 ≤ c) :
    volume (Ioo 0 Mw ∩ Iic c) = ENNReal.ofReal (min Mw c) := by
  rcases le_total Mw c with h | h
  · have : Ioo 0 Mw ∩ Iic c = Ioo 0 Mw := inter_eq_left.2 fun y hy => mem_Iic.2 (by
      simp only [mem_Ioo] at hy; linarith [hy.2])
    rw [this, Real.volume_Ioo, min_eq_left h, sub_zero]
  · have : Ioo 0 Mw ∩ Iic c = Ioc 0 c ∩ Iio Mw := by
      ext y; simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc, mem_Iio]; tauto
    rw [min_eq_right h]
    rcases h.lt_or_eq with hlt | heq
    · have : Ioo 0 Mw ∩ Iic c = Ioc 0 c := by
        ext y; simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
      rw [this, Real.volume_Ioc, sub_zero]
    · subst heq
      have : Ioo 0 c ∩ Iic c = Ioo 0 c := inter_eq_left.2 fun y hy => mem_Iic.2 hy.2.le
      rw [this, Real.volume_Ioo, sub_zero]

/-- The pushforward of Lebesgue measure on `(0, U[0,w))` under `Q` is `U` restricted to
`[0, w)`, for every `w ≤ wh`. -/
lemma Q_map (hwh : 0 ≤ wh) (hfin : U (Ico 0 wh) ≠ ∞) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ wh) :
    (volume.restrict (Ioo 0 (U (Ico 0 w)).toReal)).map (Q U wh) = U.restrict (Ico 0 w) := by
  have hfinw : U (Ico 0 w) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono (Ico_subset_Ico_right hw))
  set Mw := (U (Ico 0 w)).toReal with hMw
  have hMw0 : 0 ≤ Mw := ENNReal.toReal_nonneg
  have hMwM : Mw ≤ Mt U wh := ENNReal.toReal_mono hfin (measure_mono (Ico_subset_Ico_right hw))
  haveI : IsFiniteMeasure ((volume.restrict (Ioo 0 Mw)).map (Q U wh)) := by
    refine ⟨?_⟩
    rw [Measure.map_apply (Q_meas hwh hfin) MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply (Q_meas hwh hfin) measurableSet_Iic,
    Measure.restrict_apply (measurableSet_Iic.preimage (Q_meas hwh hfin)),
    Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge x 0 with hx0 | hx0
  · have h1 : Q U wh ⁻¹' Iic x ∩ Ioo 0 Mw = ∅ := by
      refine eq_empty_of_forall_notMem fun v hv => ?_
      have := Q_nonneg hwh hfin v
      simp only [mem_inter_iff, mem_preimage, mem_Iic] at hv
      linarith [hv.1]
    have h2 : Iic x ∩ Ico 0 w = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => ?_
      simp only [mem_inter_iff, mem_Iic, mem_Ico] at hy
      linarith [hy.1, hy.2.1]
    rw [h1, h2, measure_empty, measure_empty]
  rcases lt_or_ge x wh with hxwh | hxwh
  · -- Galois on `(0, Mw)`
    have h1 : Q U wh ⁻¹' Iic x ∩ Ioo 0 Mw = Ioo 0 Mw ∩ Iic (Φ U wh x) := by
      ext v
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo]
      constructor
      · rintro ⟨h, hv0, hvM⟩
        exact ⟨⟨hv0, hvM⟩, (Q_le_iff hwh hfin (by linarith) ⟨hx0, hxwh.le⟩).1 h⟩
      · rintro ⟨⟨hv0, hvM⟩, h⟩
        exact ⟨(Q_le_iff hwh hfin (by linarith) ⟨hx0, hxwh.le⟩).2 h, hv0, hvM⟩
    rw [h1, vol_Ioo_inter Mw _ hMw0 (Φ_nonneg x)]
    rcases lt_or_ge x w with hxw | hxw
    · have h2 : Iic x ∩ Ico 0 w = Icc 0 x := by
        ext y; simp only [mem_inter_iff, mem_Iic, mem_Ico, mem_Icc]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
      have hΦ : Φ U wh x = (U (Icc 0 x)).toReal := Φ_eq_W hx0 hxwh
      have hle : Φ U wh x ≤ Mw := by
        rw [hΦ]; exact ENNReal.toReal_mono hfinw (measure_mono (Icc_subset_Ico_right hxw))
      rw [h2, min_eq_right hle, hΦ, ENNReal.ofReal_toReal
        (ne_top_of_le_ne_top hfinw (measure_mono (Icc_subset_Ico_right hxw)))]
    · have h2 : Iic x ∩ Ico 0 w = Ico 0 w := inter_eq_right.2 fun y hy => mem_Iic.2 (by
        simp only [mem_Ico] at hy; linarith [hy.2])
      have hge : Mw ≤ Φ U wh x := by
        unfold Φ
        refine ENNReal.toReal_mono (ne_top_of_le_ne_top hfin (measure_mono inter_subset_left))
          (measure_mono fun y hy => ?_)
        simp only [mem_Ico] at hy
        exact ⟨⟨hy.1, by linarith [hy.2]⟩, mem_Iic.2 (by linarith [hy.2])⟩
      rw [h2, min_eq_left hge, hMw, ENNReal.ofReal_toReal hfinw]
  · have h1 : Q U wh ⁻¹' Iic x ∩ Ioo 0 Mw = Ioo 0 Mw := inter_eq_right.2 fun v _ =>
      mem_preimage.2 (mem_Iic.2 ((Q_le hwh hfin v).trans hxwh))
    have h2 : Iic x ∩ Ico 0 w = Ico 0 w := inter_eq_right.2 fun y hy => mem_Iic.2 (by
      simp only [mem_Ico] at hy; linarith [hy.2])
    rw [h1, h2, Real.volume_Ioo, sub_zero, hMw, ENNReal.ofReal_toReal hfinw]

lemma integral_Q (hwh : 0 ≤ wh) (hfin : U (Ico 0 wh) ≠ ∞) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ wh)
    (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ x in Ico 0 w, g x ∂U = ∫ v in Ioo 0 (U (Ico 0 w)).toReal, g (Q U wh v) := by
  rw [← Q_map hwh hfin hw0 hw, integral_map (Q_meas hwh hfin).aemeasurable
    hg.aestronglyMeasurable]

/-- Convexity of the quantile function when `x ↦ U[0,x]` is concave on `[0, wh]`. -/
lemma Q_convex (hwh : 0 ≤ wh) (hfin : U (Ico 0 wh) ≠ ∞) (hfin2 : U (Icc 0 wh) ≠ ∞)
    (hconc : ConcaveOn ℝ (Icc 0 wh) (fun x => (U (Icc 0 x)).toReal)) :
    ConvexOn ℝ (Icc 0 (Mt U wh)) (Q U wh) := by
  -- `Φ = min(W, M)` on `[0, wh]`
  have hΦc : ConcaveOn ℝ (Icc 0 wh) (Φ U wh) := by
    have hmin := hconc.inf (concaveOn_const (Mt U wh) (convex_Icc 0 wh))
    refine hmin.congr fun x hx => ?_
    simp only [Pi.inf_apply]
    rcases hx.2.lt_or_eq with hlt | heq
    · rw [Φ_eq_W hx.1 hlt, min_eq_left]
      exact ENNReal.toReal_mono hfin (measure_mono (Icc_subset_Ico_right hlt))
    · subst heq
      rw [Φ_top le_rfl, min_eq_right]
      exact ENNReal.toReal_mono hfin2 (measure_mono Ico_subset_Icc_self)
  refine ⟨convex_Icc _ _, ?_⟩
  intro v1 hv1 v2 hv2 a b ha hb hab
  simp only [smul_eq_mul]
  have hx1 : Q U wh v1 ∈ Icc 0 wh := ⟨Q_nonneg hwh hfin v1, Q_le hwh hfin v1⟩
  have hx2 : Q U wh v2 ∈ Icc 0 wh := ⟨Q_nonneg hwh hfin v2, Q_le hwh hfin v2⟩
  have hΦ1 : v1 ≤ Φ U wh (Q U wh v1) := Φ_Q hwh hfin hv1.2
  have hΦ2 : v2 ≤ Φ U wh (Q U wh v2) := Φ_Q hwh hfin hv2.2
  have hpt : a • Q U wh v1 + b • Q U wh v2 ∈ Icc 0 wh := (convex_Icc 0 wh) hx1 hx2 ha hb hab
  have hcc := hΦc.2 hx1 hx2 ha hb hab
  simp only [smul_eq_mul] at hpt hcc
  have hv : a * v1 + b * v2 ≤ Mt U wh := by
    have h1 := mul_le_mul_of_nonneg_left hv1.2 ha
    have h2 := mul_le_mul_of_nonneg_left hv2.2 hb
    have h3 : a * Mt U wh + b * Mt U wh = Mt U wh := by rw [← add_mul, hab, one_mul]
    linarith
  rw [Q_le_iff hwh hfin hv hpt]
  have h1 := mul_le_mul_of_nonneg_left hΦ1 ha
  have h2 := mul_le_mul_of_nonneg_left hΦ2 hb
  linarith

/-- Gaps of the shortened quantile function are at most `t` times the original gaps. -/
lemma Q_scale {Qf : ℝ → ℝ} {M : ℝ} (hconv : ConvexOn ℝ (Icc 0 M) Qf) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ M) :
    Qf (t * v) - Qf (t * u) ≤ t * (Qf v - Qf u) := by
  rcases huv.lt_or_eq with huv | huv
  swap
  · subst huv; simp
  rcases ht1.lt_or_eq with ht1 | ht1
  swap
  · subst ht1; simp
  have htu : t * u ≤ u := by nlinarith
  have htv : t * v ≤ v := by nlinarith
  have htuv : t * u < t * v := mul_lt_mul_of_pos_left huv ht0
  have hmem : ∀ x, 0 ≤ x → x ≤ M → x ∈ Icc 0 M := fun x h1 h2 => ⟨h1, h2⟩
  have hM : 0 ≤ M := hu.trans (huv.le.trans hv)
  have m_tu := hmem (t * u) (mul_nonneg ht0.le hu) (by linarith)
  have m_tv := hmem (t * v) (mul_nonneg ht0.le (hu.trans huv.le)) (by linarith)
  have m_u := hmem u hu (by linarith)
  have m_v := hmem v (by linarith) hv
  have s1 := hconv.secant_mono m_tu m_tv m_v htuv.ne' (by linarith) htv
  have s2 := hconv.secant_mono m_v m_tu m_u (by linarith) (by linarith) htu
  have e1 : (Qf v - Qf (t * u)) / (v - t * u) = (Qf (t * u) - Qf v) / (t * u - v) := by
    rw [← neg_div_neg_eq]; congr 1 <;> ring
  have e2 : (Qf u - Qf v) / (u - v) = (Qf v - Qf u) / (v - u) := by
    rw [← neg_div_neg_eq]; congr 1 <;> ring
  have key : (Qf (t * v) - Qf (t * u)) / (t * v - t * u) ≤ (Qf v - Qf u) / (v - u) := by
    calc (Qf (t * v) - Qf (t * u)) / (t * v - t * u)
        ≤ (Qf v - Qf (t * u)) / (v - t * u) := s1
      _ = (Qf (t * u) - Qf v) / (t * u - v) := e1
      _ ≤ (Qf u - Qf v) / (u - v) := s2
      _ = (Qf v - Qf u) / (v - u) := e2
  have hvu : 0 < v - u := by linarith
  rw [show t * v - t * u = t * (v - u) by ring, div_le_div_iff₀ (by positivity) hvu] at key
  nlinarith

/-- `∫_{(0, tM)} g = t ∫_{(0, M)} g(t ·)`. -/
lemma integral_scale (g : ℝ → ℝ) {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M) :
    ∫ v in Ioo 0 (t * M), g v = t * ∫ u in Ioo 0 M, g (t * u) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by positivity), ← intervalIntegral.integral_of_le hM,
    intervalIntegral.integral_comp_mul_left (fun u => g u) ht.ne', mul_zero, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

/-- Running averages of a nondecreasing function lie below its full average. -/
lemma running_avg {e : ℝ → ℝ} {M x : ℝ} (he : MonotoneOn e (Icc 0 M)) (hx0 : 0 ≤ x) (hxM : x ≤ M)
    (hint : IntegrableOn e (Icc 0 M)) :
    M * ∫ u in Ioo 0 x, e u ≤ x * ∫ u in Ioo 0 M, e u := by
  have hIx : IntegrableOn e (uIcc 0 x) := by
    rw [uIcc_of_le hx0]; exact hint.mono_set (Icc_subset_Icc le_rfl hxM)
  have hIxM : IntegrableOn e (uIcc x M) := by
    rw [uIcc_of_le hxM]; exact hint.mono_set (Icc_subset_Icc hx0 le_rfl)
  have c1 : ∫ u in Ioo 0 x, e u = ∫ u in (0)..x, e u := by
    rw [intervalIntegral.integral_of_le hx0, integral_Ioc_eq_integral_Ioo]
  have c2 : ∫ u in Ioo 0 M, e u = ∫ u in (0)..M, e u := by
    rw [intervalIntegral.integral_of_le (hx0.trans hxM), integral_Ioc_eq_integral_Ioo]
  have hadd := intervalIntegral.integral_add_adjacent_intervals hIx.intervalIntegrable
    hIxM.intervalIntegrable
  have hA : ∫ u in (0)..x, e u ≤ x * e x := by
    have := intervalIntegral.integral_mono_on hx0 hIx.intervalIntegrable
      (intervalIntegrable_const (c := e x)) fun u hu =>
        he ⟨hu.1, hu.2.trans hxM⟩ ⟨hx0, hxM⟩ hu.2
    simpa [intervalIntegral.integral_const, mul_comm] using this
  have hB : (M - x) * e x ≤ ∫ u in x..M, e u := by
    have := intervalIntegral.integral_mono_on hxM (intervalIntegrable_const (c := e x))
      hIxM.intervalIntegrable fun u hu => he ⟨hx0, hxM⟩ ⟨hx0.trans hu.1, hu.2⟩ hu.1
    simpa [intervalIntegral.integral_const, mul_comm] using this
  rw [c1, c2, ← hadd]
  have hMx : 0 ≤ M - x := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hA hMx, mul_le_mul_of_nonneg_left hB hx0]

lemma ioo_split {f : ℝ → ℝ} {M x : ℝ} (hx0 : 0 ≤ x) (hxM : x ≤ M) (hf : IntegrableOn f (Icc 0 M)) :
    ∫ u in Ioo 0 M, f u = (∫ u in Ioo 0 x, f u) + ∫ u in Ioo x M, f u := by
  have hIx : IntegrableOn f (uIcc 0 x) := by
    rw [uIcc_of_le hx0]; exact hf.mono_set (Icc_subset_Icc le_rfl hxM)
  have hIxM : IntegrableOn f (uIcc x M) := by
    rw [uIcc_of_le hxM]; exact hf.mono_set (Icc_subset_Icc hx0 le_rfl)
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (hx0.trans hxM),
    ← intervalIntegral.integral_of_le hx0, ← intervalIntegral.integral_of_le hxM]
  exact (intervalIntegral.integral_add_adjacent_intervals hIx.intervalIntegrable
      hIxM.intervalIntegrable).symm

/-- Lower stop-loss comparison on `(0, M)`. -/
lemma stoploss {X1 X2 : ℝ → ℝ} {M : ℝ} (hM : 0 < M) (h1 : MonotoneOn X1 (Icc 0 M))
    (hd : MonotoneOn (fun u => X2 u - X1 u) (Icc 0 M))
    (hi1 : IntegrableOn X1 (Icc 0 M)) (hi2 : IntegrableOn X2 (Icc 0 M))
    (hmean : ∫ u in Ioo 0 M, X1 u = ∫ u in Ioo 0 M, X2 u) (k : ℝ) :
    ∫ u in Ioo 0 M, max (k - X1 u) 0 ≤ ∫ u in Ioo 0 M, max (k - X2 u) 0 := by
  classical
  set A := {u | u ∈ Icc 0 M ∧ X1 u < k} with hA
  set xs : ℝ := if A.Nonempty then sSup A else 0 with hxs
  have hAbdd : BddAbove A := ⟨M, fun u hu => hu.1.2⟩
  have hxs0 : 0 ≤ xs := by
    rw [hxs]; split_ifs with hne
    · obtain ⟨a, ha⟩ := hne; exact ha.1.1.trans (le_csSup hAbdd ha)
    · exact le_rfl
  have hxsM : xs ≤ M := by
    rw [hxs]; split_ifs with hne
    · exact csSup_le hne fun u hu => hu.1.2
    · exact hM.le
  have hbelow : ∀ u ∈ Ioo 0 xs, X1 u < k := by
    intro u hu
    have hne : A.Nonempty := by
      by_contra hne; rw [hxs, if_neg hne] at hu; exact absurd hu.2 (not_lt.2 hu.1.le)
    rw [hxs, if_pos hne] at hu
    obtain ⟨a, ha, hua⟩ := exists_lt_of_lt_csSup hne hu.2
    exact lt_of_le_of_lt (h1 ⟨hu.1.le, hua.le.trans ha.1.2⟩ ha.1 hua.le) ha.2
  have habove : ∀ u ∈ Ioo xs M, k ≤ X1 u := by
    intro u hu
    by_contra hlt
    push_neg at hlt
    have hmem : u ∈ A := ⟨⟨hxs0.trans hu.1.le, hu.2.le⟩, hlt⟩
    have hne : A.Nonempty := ⟨u, hmem⟩
    have := le_csSup hAbdd hmem
    rw [hxs, if_pos hne] at hu
    linarith [hu.1]
  have hint1 : IntegrableOn (fun u => max (k - X1 u) 0) (Icc 0 M) :=
    ((integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (by simp)).sub hi1).sup (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp))
  have hint2 : IntegrableOn (fun u => max (k - X2 u) 0) (Icc 0 M) :=
    ((integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (by simp)).sub hi2).sup (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp))
  have hconst : IntegrableOn (fun _ : ℝ => k) (Icc 0 M) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  have hsub : ∀ {a b : ℝ}, 0 ≤ a → b ≤ M → Ioo a b ⊆ Icc 0 M := fun ha hb u hu =>
    ⟨ha.trans hu.1.le, hu.2.le.trans hb⟩
  -- LHS reduces to `∫_{(0,xs)} (k - X1)`
  have hL : ∫ u in Ioo 0 M, max (k - X1 u) 0 = ∫ u in Ioo 0 xs, (k - X1 u) := by
    rw [ioo_split hxs0 hxsM hint1]
    beta_reduce
    have e1 : ∫ u in Ioo 0 xs, max (k - X1 u) 0 = ∫ u in Ioo 0 xs, (k - X1 u) :=
      setIntegral_congr_fun measurableSet_Ioo fun u hu => max_eq_left (by linarith [hbelow u hu])
    have e2 : ∫ u in Ioo xs M, max (k - X1 u) 0 = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
        fun u hu => max_eq_right (by linarith [habove u hu])]
      simp
    rw [e1, e2, add_zero]
  -- running average of the difference
  have hdiff : ∫ u in Ioo 0 xs, (X2 u - X1 u) ≤ 0 := by
    have hiD : IntegrableOn (fun u => X2 u - X1 u) (Icc 0 M) := hi2.sub hi1
    have hra := running_avg hd hxs0 hxsM hiD
    have htot : ∫ u in Ioo 0 M, (X2 u - X1 u) = 0 := by
      rw [integral_sub (hi2.mono_set (hsub le_rfl le_rfl)) (hi1.mono_set (hsub le_rfl le_rfl)),
        hmean, sub_self]
    rw [htot, mul_zero] at hra
    nlinarith
  have hsplit : ∫ u in Ioo 0 xs, (k - X1 u)
      = (∫ u in Ioo 0 xs, (k - X2 u)) + ∫ u in Ioo 0 xs, (X2 u - X1 u) := by
    have i1 : IntegrableOn (fun u => k - X2 u) (Ioo 0 xs) :=
      ((hconst.sub hi2 : IntegrableOn (fun u => k - X2 u) (Icc 0 M))).mono_set (hsub le_rfl hxsM)
    have i2 : IntegrableOn (fun u => X2 u - X1 u) (Ioo 0 xs) :=
      ((hi2.sub hi1 : IntegrableOn (fun u => X2 u - X1 u) (Icc 0 M))).mono_set (hsub le_rfl hxsM)
    rw [← integral_add i1 i2]
    congr 1; ext u; ring
  rw [hL, hsplit]
  calc (∫ u in Ioo 0 xs, (k - X2 u)) + ∫ u in Ioo 0 xs, (X2 u - X1 u)
      ≤ ∫ u in Ioo 0 xs, (k - X2 u) := by linarith
    _ ≤ ∫ u in Ioo 0 xs, max (k - X2 u) 0 :=
        setIntegral_mono_on ((hconst.sub hi2).mono_set (hsub le_rfl hxsM))
          (hint2.mono_set (hsub le_rfl hxsM)) measurableSet_Ioo fun u _ => le_max_left _ _
    _ ≤ ∫ u in Ioo 0 M, max (k - X2 u) 0 := by
        rw [ioo_split hxs0 hxsM hint2]
        beta_reduce
        have : 0 ≤ ∫ u in Ioo xs M, max (k - X2 u) 0 :=
          setIntegral_nonneg measurableSet_Ioo fun u _ => le_max_right _ _
        linarith

lemma icc_const_int (M c : ℝ) : IntegrableOn (fun _ : ℝ => c) (Icc 0 M) :=
  integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)

lemma ioo_sub_const {g : ℝ → ℝ} {a b M : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M) (c : ℝ)
    (hg : IntegrableOn g (Icc 0 M)) :
    ∫ u in Ioo a b, (c - g u) = (b - a) * c - ∫ u in Ioo a b, g u := by
  have hs : Ioo a b ⊆ Icc 0 M := fun u hu => ⟨ha.trans hu.1.le, hu.2.le.trans hb⟩
  rw [integral_sub ((icc_const_int M c).mono_set hs) (hg.mono_set hs), setIntegral_const,
    smul_eq_mul, Real.volume_real_Ioo_of_le hab]

lemma ioo_const_sub {g : ℝ → ℝ} {a b M : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M) (c : ℝ)
    (hg : IntegrableOn g (Icc 0 M)) :
    ∫ u in Ioo a b, (g u - c) = (∫ u in Ioo a b, g u) - (b - a) * c := by
  have hs : Ioo a b ⊆ Icc 0 M := fun u hu => ⟨ha.trans hu.1.le, hu.2.le.trans hb⟩
  rw [integral_sub (hg.mono_set hs) ((icc_const_int M c).mono_set hs), setIntegral_const,
    smul_eq_mul, Real.volume_real_Ioo_of_le hab]

/-- Mirror contraction (Lemma D.1, first inequality) in quantile form. -/
lemma mirror_contract {Qf : ℝ → ℝ} {M t h p : ℝ} (hM : 0 < M) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hh : 0 < h) (hp : 0 < p) (hmono : Monotone Qf) (hconv : ConvexOn ℝ (Icc 0 M) Qf)
    (c' : ℝ) :
    ∫ u in Ioo 0 M, (h * max (Qf (t * u) - Qf (t * (h / (h + p) * M))) 0
        + p * max (Qf (t * (h / (h + p) * M)) - Qf (t * u)) 0)
      ≤ t * ∫ u in Ioo 0 M, (h * max (Qf u - c') 0 + p * max (c' - Qf u) 0) := by
  set x := h / (h + p) * M with hx
  have hhp : 0 < h + p := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hxM : x ≤ M := by
    rw [hx]; have : h / (h + p) ≤ 1 := by rw [div_le_one hhp]; linarith
    nlinarith
  have hpx : p * x = h * (M - x) := by rw [hx]; field_simp; ring
  set c := Qf (t * x) with hc
  have hint : IntegrableOn Qf (Icc 0 M) := (hmono.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have hintt : IntegrableOn (fun u => Qf (t * u)) (Icc 0 M) :=
    (((hmono.comp fun a b hab => mul_le_mul_of_nonneg_left hab ht0.le).monotoneOn
      _).integrableOn_isCompact isCompact_Icc : IntegrableOn (Qf ∘ fun u => t * u) (Icc 0 M) volume)
  have hcont : ∀ {f : ℝ → ℝ}, IntegrableOn f (Icc 0 M) → IntegrableOn (fun u => h * max (f u - c') 0
      + p * max (c' - f u) 0) (Icc 0 M) := by
    intro f hf
    exact (((hf.sub (icc_const_int M c')).sup (icc_const_int M 0)).const_mul h).add
      ((((icc_const_int M c').sub hf).sup (icc_const_int M 0)).const_mul p)
  -- LHS in closed form
  have hL : ∫ u in Ioo 0 M, (h * max (Qf (t * u) - c) 0 + p * max (c - Qf (t * u)) 0)
      = h * ((∫ u in Ioo x M, Qf (t * u)) - (M - x) * c) + p * (x * c - ∫ u in Ioo 0 x, Qf (t * u)) := by
    have hi : IntegrableOn (fun u => h * max (Qf (t * u) - c) 0 + p * max (c - Qf (t * u)) 0) (Icc 0 M) := by
      have := (((hintt.sub (icc_const_int M c)).sup (icc_const_int M 0)).const_mul h).add
        ((((icc_const_int M c).sub hintt).sup (icc_const_int M 0)).const_mul p)
      exact this
    rw [ioo_split hx0 hxM hi]
    beta_reduce
    have e1 : ∫ u in Ioo 0 x, (h * max (Qf (t * u) - c) 0 + p * max (c - Qf (t * u)) 0)
        = ∫ u in Ioo 0 x, p * (c - Qf (t * u)) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      have : Qf (t * u) ≤ c := hmono (mul_le_mul_of_nonneg_left hu.2.le ht0.le)
      rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
    have e2 : ∫ u in Ioo x M, (h * max (Qf (t * u) - c) 0 + p * max (c - Qf (t * u)) 0)
        = ∫ u in Ioo x M, h * (Qf (t * u) - c) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      have : c ≤ Qf (t * u) := hmono (mul_le_mul_of_nonneg_left hu.1.le ht0.le)
      rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    rw [e1, e2, integral_const_mul, integral_const_mul, ioo_sub_const le_rfl hx0 hxM c hintt,
      ioo_const_sub hx0 hxM le_rfl c hintt]
    ring
  -- RHS lower bound
  have hR : h * ((∫ u in Ioo x M, Qf u) - (M - x) * c') + p * (x * c' - ∫ u in Ioo 0 x, Qf u)
      ≤ ∫ u in Ioo 0 M, (h * max (Qf u - c') 0 + p * max (c' - Qf u) 0) := by
    rw [ioo_split hx0 hxM (hcont hint)]
    beta_reduce
    have e1 : p * (x * c' - ∫ u in Ioo 0 x, Qf u)
        ≤ ∫ u in Ioo 0 x, (h * max (Qf u - c') 0 + p * max (c' - Qf u) 0) := by
      have eq1 : ∫ u in Ioo 0 x, p * (c' - Qf u) = p * (x * c' - ∫ u in Ioo 0 x, Qf u) := by
        rw [integral_const_mul, ioo_sub_const le_rfl hx0 hxM c' hint, sub_zero]
      rw [← eq1]
      have hI1 : IntegrableOn (fun u => p * (c' - Qf u)) (Icc 0 M) volume :=
        ((icc_const_int M c').sub hint).const_mul p
      refine setIntegral_mono_on (IntegrableOn.mono_set hI1
        (fun u (hu : u ∈ Ioo 0 x) => ⟨hu.1.le, hu.2.le.trans hxM⟩)) ((hcont hint).mono_set
        (fun u hu => ⟨hu.1.le, hu.2.le.trans hxM⟩)) measurableSet_Ioo fun u _ => ?_
      have h1 : 0 ≤ h * max (Qf u - c') 0 := mul_nonneg hh.le (le_max_right _ _)
      have h2 : p * (c' - Qf u) ≤ p * max (c' - Qf u) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hp.le
      linarith
    have e2 : h * ((∫ u in Ioo x M, Qf u) - (M - x) * c')
        ≤ ∫ u in Ioo x M, (h * max (Qf u - c') 0 + p * max (c' - Qf u) 0) := by
      have eq2 : ∫ u in Ioo x M, h * (Qf u - c') = h * ((∫ u in Ioo x M, Qf u) - (M - x) * c') := by
        rw [integral_const_mul, ioo_const_sub hx0 hxM le_rfl c' hint]
      rw [← eq2]
      have hI2 : IntegrableOn (fun u => h * (Qf u - c')) (Icc 0 M) volume :=
        (hint.sub (icc_const_int M c')).const_mul h
      refine setIntegral_mono_on (IntegrableOn.mono_set hI2
        (fun u (hu : u ∈ Ioo x M) => ⟨hx0.trans hu.1.le, hu.2.le⟩)) ((hcont hint).mono_set
        (fun u hu => ⟨hx0.trans hu.1.le, hu.2.le⟩)) measurableSet_Ioo fun u _ => ?_
      have h1 : 0 ≤ p * max (c' - Qf u) 0 := mul_nonneg hp.le (le_max_right _ _)
      have h2 : h * (Qf u - c') ≤ h * max (Qf u - c') 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hh.le
      linarith
    linarith
  -- the gap function `D(u) = t Q(u) - Q(t u)` is nondecreasing
  set D : ℝ → ℝ := fun u => t * Qf u - Qf (t * u) with hD
  have hDmono : MonotoneOn D (Icc 0 M) := by
    intro u hu v hv huv
    have := Q_scale hconv ht0 ht1 hu.1 huv hv.2
    simp only [hD]
    linarith
  have hDint : IntegrableOn D (Icc 0 M) := (hint.const_mul t).sub hintt
  have hD1 : ∫ u in Ioo 0 x, D u ≤ x * D x := by
    have := setIntegral_mono_on (hDint.mono_set (fun u hu => ⟨hu.1.le, hu.2.le.trans hxM⟩))
      (icc_const_int M (D x) |>.mono_set (fun u hu => ⟨hu.1.le, hu.2.le.trans hxM⟩))
      measurableSet_Ioo fun u hu => hDmono ⟨hu.1.le, hu.2.le.trans hxM⟩ ⟨hx0, hxM⟩ hu.2.le
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hx0, sub_zero] at this
    exact this
  have hD2 : (M - x) * D x ≤ ∫ u in Ioo x M, D u := by
    have := setIntegral_mono_on (icc_const_int M (D x) |>.mono_set
      (fun u hu => ⟨hx0.trans hu.1.le, hu.2.le⟩))
      (hDint.mono_set (fun u hu => ⟨hx0.trans hu.1.le, hu.2.le⟩))
      measurableSet_Ioo fun u hu => hDmono ⟨hx0, hxM⟩ ⟨hx0.trans hu.1.le, hu.2.le⟩ hu.1.le
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hxM] at this
    exact this
  have hIt : IntegrableOn (fun u => t * Qf u) (Icc 0 M) volume := hint.const_mul t
  have hDs1 : ∫ u in Ioo 0 x, D u = t * (∫ u in Ioo 0 x, Qf u) - ∫ u in Ioo 0 x, Qf (t * u) := by
    rw [integral_sub (IntegrableOn.mono_set hIt
      (fun u (hu : u ∈ Ioo 0 x) => ⟨hu.1.le, hu.2.le.trans hxM⟩))
      (hintt.mono_set (fun u hu => ⟨hu.1.le, hu.2.le.trans hxM⟩)), integral_const_mul]
  have hDs2 : ∫ u in Ioo x M, D u = t * (∫ u in Ioo x M, Qf u) - ∫ u in Ioo x M, Qf (t * u) := by
    rw [integral_sub (IntegrableOn.mono_set hIt
      (fun u (hu : u ∈ Ioo x M) => ⟨hx0.trans hu.1.le, hu.2.le⟩))
      (hintt.mono_set (fun u hu => ⟨hx0.trans hu.1.le, hu.2.le⟩)), integral_const_mul]
  rw [hL]
  have key : p * ∫ u in Ioo 0 x, D u ≤ h * ∫ u in Ioo x M, D u := by
    have h1 := mul_le_mul_of_nonneg_left hD1 hp.le
    have h2 := mul_le_mul_of_nonneg_left hD2 hh.le
    have h3 : p * (x * D x) = h * ((M - x) * D x) := by
      rw [← mul_assoc, hpx, mul_assoc]
    linarith
  have hcc : h * ((M - x) * c) = p * (x * c) := by rw [← mul_assoc, ← hpx, mul_assoc]
  have hcc' : h * ((M - x) * c') = p * (x * c') := by rw [← mul_assoc, ← hpx, mul_assoc]
  have htR := mul_le_mul_of_nonneg_left hR ht0.le
  nlinarith

section hold

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

/-- The hinge part `A(y) = ∫ (y - ζ)⁺ dν(ζ)`. -/
def Ahinge (y : ℝ) : ℝ := ∫ ζ, max (y - ζ) 0 ∂ν

lemma hinge_int (hν : Integrable id ν) (y : ℝ) : Integrable (fun ζ => max (y - ζ) 0) ν := by
  have hb : Integrable (fun ζ : ℝ => |y| + |ζ|) ν :=
    (integrable_const |y|).add (by simpa [Real.norm_eq_abs] using hν.norm)
  refine Integrable.mono' hb ?_ (ae_of_all _ fun ζ => ?_)
  · exact (by fun_prop : Continuous fun ζ : ℝ => max (y - ζ) 0).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have := neg_abs_le ζ
    have := le_abs_self y
    linarith

lemma Ahinge_lip (hν : Integrable id ν) (y1 y2 : ℝ) :
    |Ahinge ν y1 - Ahinge ν y2| ≤ |y1 - y2| := by
  unfold Ahinge
  rw [← integral_sub (hinge_int ν hν y1) (hinge_int ν hν y2)]
  refine (abs_integral_le_integral_abs).trans ?_
  have : ∀ ζ, |max (y1 - ζ) 0 - max (y2 - ζ) 0| ≤ |y1 - y2| := fun ζ => by
    have := abs_max_sub_max_le_abs (y1 - ζ) (y2 - ζ) 0
    simpa using this
  calc ∫ ζ, |max (y1 - ζ) 0 - max (y2 - ζ) 0| ∂ν ≤ ∫ _ζ, |y1 - y2| ∂ν :=
        integral_mono ((hinge_int ν hν y1).sub (hinge_int ν hν y2)).abs (integrable_const _) this
    _ = |y1 - y2| := by simp

lemma Ahinge_cont (hν : Integrable id ν) : Continuous (Ahinge ν) :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b => by
    simpa [Real.dist_eq] using Ahinge_lip ν hν a b)

lemma Ahinge_nonneg (y : ℝ) : 0 ≤ Ahinge ν y := integral_nonneg fun _ => le_max_right _ _

lemma hinge_prod_int (hν : Integrable id ν) {X : ℝ → ℝ} {M B : ℝ} (hX : Measurable X)
    (hXb : ∀ u, |X u| ≤ B) (c : ℝ) :
    Integrable (Function.uncurry fun u ζ : ℝ => max (c - ζ - X u) 0)
      ((volume.restrict (Ioo 0 M)).prod ν) := by
  refine Integrable.mono' (g := fun q : ℝ × ℝ => |c| + B + ‖q.2‖) ?_ ?_ (ae_of_all _ fun q => ?_)
  · exact (integrable_const _).add (hν.norm.comp_snd (volume.restrict (Ioo 0 M)))
  · exact (by
      have : Measurable (Function.uncurry fun u ζ : ℝ => max (c - ζ - X u) 0) :=
        ((measurable_const.sub measurable_snd).sub (hX.comp measurable_fst)).max measurable_const
      exact this.aestronglyMeasurable)
  · simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    have hB : 0 ≤ B := (abs_nonneg _).trans (hXb 0)
    refine max_le ?_ (add_nonneg (add_nonneg (abs_nonneg c) hB) (abs_nonneg _))
    have h1 := neg_abs_le q.2
    have h2 := le_abs_self c
    have h3 := hXb q.1
    have h4 := neg_abs_le (X q.1)
    linarith

/-- Fubini for the hinge part. -/
lemma hinge_swap (hν : Integrable id ν) {X : ℝ → ℝ} {M B : ℝ} (hX : Measurable X)
    (hXb : ∀ u, |X u| ≤ B) (c : ℝ) :
    ∫ u in Ioo 0 M, Ahinge ν (c - X u) = ∫ ζ, (∫ u in Ioo 0 M, max (c - ζ - X u) 0) ∂ν := by
  unfold Ahinge
  have e : ∀ u ζ, max (c - X u - ζ) 0 = max (c - ζ - X u) 0 := fun u ζ => by ring_nf
  simp_rw [e]
  exact integral_integral_swap (hinge_prod_int ν hν hX hXb c)

/-- Integrability of `u ↦ A(c - X u)` on `(0, M)`. -/
lemma Ahinge_comp_int (hν : Integrable id ν) {X : ℝ → ℝ} {M B : ℝ} (hX : Measurable X)
    (hXb : ∀ u, |X u| ≤ B) (c : ℝ) :
    IntegrableOn (fun u => Ahinge ν (c - X u)) (Ioo 0 M) := by
  refine Measure.integrableOn_of_bounded (M := Ahinge ν (|c| + B) + |c| + B + |c| + B)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    ((Ahinge_cont ν hν).measurable.comp (measurable_const.sub hX)).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Ahinge_nonneg ν _)]
  have h1 := Ahinge_lip ν hν (c - X u) (|c| + B)
  have h2 := abs_le.1 (hXb u)
  have h3 := abs_sub_abs_le_abs_sub (c - X u) (|c| + B)
  have h4 : |c - X u - (|c| + B)| ≤ |c| + B + |c| + B := by
    refine (abs_sub _ _).trans ?_
    have := abs_sub (c) (X u)
    have := abs_le.1 (hXb u)
    have hB : 0 ≤ B := le_trans (abs_nonneg _) (hXb 0)
    rw [abs_of_nonneg (by positivity : 0 ≤ |c| + B)]
    linarith [abs_nonneg c, hXb u]
  have := (abs_le.1 h1).1
  have := (abs_le.1 h1).2
  linarith [Ahinge_nonneg ν (|c| + B)]

/-- Holding and backlog contraction (Lemma D.1, outer inequality of the second display),
in quantile form, for `F(y) = (H + p) A(y) - p (y - 𝔼ζ)`. -/
lemma hold_contract {Qf : ℝ → ℝ} {M t B : ℝ} (hM : 0 < M) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmono : Monotone Qf) (hconv : ConvexOn ℝ (Icc 0 M) Qf) (hQb : ∀ u, |Qf u| ≤ B)
    (hν : Integrable id ν) {Fn : ℝ → ℝ} {H p : ℝ} (hH : 0 < H) (hp : 0 < p)
    (hFeq : ∀ y, Fn y = (H + p) * Ahinge ν y - p * (y - ∫ ζ, ζ ∂ν))
    (hFconv : ConvexOn ℝ univ Fn) (Sh : ℝ) :
    ∃ S, ∫ u in Ioo 0 M, Fn (S - Qf (t * u)) ≤ ∫ u in Ioo 0 M, Fn (Sh - Qf u) := by
  set e := ∫ ζ, ζ ∂ν with he
  have hB : 0 ≤ B := (abs_nonneg _).trans (hQb 0)
  have hQm : Measurable Qf := hmono.measurable
  have hQtm : Measurable fun u => Qf (t * u) := hQm.comp (measurable_const_mul t)
  have hmonot : Monotone fun u => Qf (t * u) :=
    hmono.comp fun a b hab => mul_le_mul_of_nonneg_left hab ht0.le
  have hint : IntegrableOn Qf (Icc 0 M) := (hmono.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have hintt : IntegrableOn (fun u => Qf (t * u)) (Icc 0 M) :=
    (hmonot.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have hsubI : Ioo (0 : ℝ) M ⊆ Icc 0 M := Ioo_subset_Icc_self
  set m := (∫ u in Ioo 0 M, Qf u) / M with hm
  set mt := (∫ u in Ioo 0 M, Qf (t * u)) / M with hmt
  have hQtb : ∀ u, |Qf (t * u)| ≤ B := fun u => hQb _
  have habsm : |m| ≤ B := by
    rw [hm, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    calc |∫ u in Ioo 0 M, Qf u| ≤ ∫ u in Ioo 0 M, |Qf u| := abs_integral_le_integral_abs
      _ ≤ ∫ _u in Ioo 0 M, B := setIntegral_mono_on (hint.mono_set hsubI).abs
          ((icc_const_int M B).mono_set hsubI) measurableSet_Ioo fun u _ => hQb u
      _ = B * M := by rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hM.le]; ring
  have habsmt : |mt| ≤ B := by
    rw [hmt, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    calc |∫ u in Ioo 0 M, Qf (t * u)| ≤ ∫ u in Ioo 0 M, |Qf (t * u)| := abs_integral_le_integral_abs
      _ ≤ ∫ _u in Ioo 0 M, B := setIntegral_mono_on (hintt.mono_set hsubI).abs
          ((icc_const_int M B).mono_set hsubI) measurableSet_Ioo fun u _ => hQtb u
      _ = B * M := by rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hM.le]; ring
  set X1 : ℝ → ℝ := fun u => Qf (t * u) - mt with hX1
  set X2 : ℝ → ℝ := fun u => t * Qf u - t * m with hX2
  have hX1m : Measurable X1 := hQtm.sub measurable_const
  have hX2m : Measurable X2 := (hQm.const_mul t).sub measurable_const
  have hX1b : ∀ u, |X1 u| ≤ B + B := fun u => by
    simp only [hX1]; exact (abs_sub _ _).trans (add_le_add (hQtb u) habsmt)
  have hX2b : ∀ u, |X2 u| ≤ B + B := fun u => by
    simp only [hX2]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos ht0]; nlinarith [hQb u, abs_nonneg (Qf u)]
    · rw [abs_mul, abs_of_pos ht0]; nlinarith [abs_nonneg m]
  have hX1i : IntegrableOn X1 (Icc 0 M) := hintt.sub (icc_const_int M mt)
  have hX2i : IntegrableOn X2 (Icc 0 M) := (hint.const_mul t).sub (icc_const_int M (t * m))
  have hX1z : ∫ u in Ioo 0 M, X1 u = 0 := by
    simp only [hX1]
    rw [ioo_const_sub le_rfl hM.le le_rfl mt hintt, sub_zero, hmt]
    field_simp
    ring
  have hX2z : ∫ u in Ioo 0 M, X2 u = 0 := by
    simp only [hX2]
    rw [ioo_const_sub le_rfl hM.le le_rfl (t * m) (hint.const_mul t), integral_const_mul, sub_zero,
      hm]
    field_simp
    ring
  -- stop-loss order between `X1` and `X2`
  have hsl : ∀ k, ∫ u in Ioo 0 M, max (k - X1 u) 0 ≤ ∫ u in Ioo 0 M, max (k - X2 u) 0 := by
    refine stoploss hM (fun a _ b _ hab => by simp only [hX1]; linarith [hmonot hab]) ?_ hX1i hX2i
      (by rw [hX1z, hX2z])
    intro a ha b hb hab
    have := Q_scale hconv ht0 ht1 ha.1 hab hb.2
    simp only [hX1, hX2]
    linarith
  -- `F(c - X)` integrated
  have hFint : ∀ {X : ℝ → ℝ}, Measurable X → (∀ u, |X u| ≤ B + B) → ∀ c : ℝ,
      ∫ u in Ioo 0 M, Fn (c - X u)
        = (H + p) * (∫ u in Ioo 0 M, Ahinge ν (c - X u))
          - p * (M * (c - e) - ∫ u in Ioo 0 M, X u) := by
    intro X hXm hXb c
    have hXi : IntegrableOn X (Ioo 0 M) := by
      refine Measure.integrableOn_of_bounded (M := B + B)
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) hXm.aestronglyMeasurable
        (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hXb u)
    have hAi := Ahinge_comp_int ν hν hXm hXb c (M := M)
    have hc1 : ∀ a : ℝ, IntegrableOn (fun _ : ℝ => a) (Ioo 0 M) := fun a =>
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (by simp)
    have hcX : IntegrableOn (fun u => c - X u) (Ioo 0 M) := (hc1 c).sub hXi
    have hlin : IntegrableOn (fun u => c - X u - e) (Ioo 0 M) := hcX.sub (hc1 e)
    simp_rw [hFeq]
    rw [integral_sub (hAi.const_mul (H + p)) (hlin.const_mul p), integral_const_mul,
      integral_const_mul, integral_sub hcX (hc1 e), integral_sub (hc1 c) hXi, setIntegral_const,
      setIntegral_const, smul_eq_mul, smul_eq_mul, Real.volume_real_Ioo_of_le hM.le]
    ring
  set c := Sh - m with hc
  refine ⟨c + mt, ?_⟩
  have hstep1 : ∫ u in Ioo 0 M, Fn (c + mt - Qf (t * u)) ≤ ∫ u in Ioo 0 M, Fn (c - X2 u) := by
    have e1 : ∀ u, c + mt - Qf (t * u) = c - X1 u := fun u => by simp only [hX1]; ring
    simp_rw [e1]
    rw [hFint hX1m hX1b c, hFint hX2m hX2b c, hX1z, hX2z]
    have hA : ∫ u in Ioo 0 M, Ahinge ν (c - X1 u) ≤ ∫ u in Ioo 0 M, Ahinge ν (c - X2 u) := by
      rw [hinge_swap ν hν hX1m hX1b c, hinge_swap ν hν hX2m hX2b c]
      refine integral_mono_of_nonneg (ae_of_all _ fun ζ => setIntegral_nonneg measurableSet_Ioo
        fun u _ => le_max_right _ _) (hinge_prod_int ν hν hX2m hX2b c).integral_prod_right
        (ae_of_all _ fun ζ => hsl (c - ζ))
    nlinarith
  -- convexity of `F`
  have hstep2 : ∫ u in Ioo 0 M, Fn (c - X2 u)
      ≤ t * (∫ u in Ioo 0 M, Fn (Sh - Qf u)) + (1 - t) * (M * Fn (Sh - m)) := by
    have hFc : Continuous Fn := by
      have : Fn = fun y => (H + p) * Ahinge ν y - p * (y - e) := funext hFeq
      rw [this]; exact ((Ahinge_cont ν hν).const_mul _).sub (by fun_prop)
    have hi1 : IntegrableOn (fun u => Fn (c - X2 u)) (Ioo 0 M) := by
      obtain ⟨K, hK⟩ := (isCompact_Icc (a := c - (B + B)) (b := c + (B + B))).exists_bound_of_continuousOn
        hFc.continuousOn
      refine Measure.integrableOn_of_bounded (M := K)
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        (hFc.measurable.comp (measurable_const.sub hX2m)).aestronglyMeasurable
        (ae_of_all _ fun u => hK _ ⟨by linarith [(abs_le.1 (hX2b u)).2], by
          linarith [(abs_le.1 (hX2b u)).1]⟩)
    have hi2 : IntegrableOn (fun u => Fn (Sh - Qf u)) (Ioo 0 M) := by
      obtain ⟨K, hK⟩ := (isCompact_Icc (a := Sh - B) (b := Sh + B)).exists_bound_of_continuousOn
        hFc.continuousOn
      refine Measure.integrableOn_of_bounded (M := K)
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        (hFc.measurable.comp (measurable_const.sub hQm)).aestronglyMeasurable
        (ae_of_all _ fun u => hK _ ⟨by linarith [(abs_le.1 (hQb u)).2], by
          linarith [(abs_le.1 (hQb u)).1]⟩)
    have hpt : ∀ u, Fn (c - X2 u) ≤ t * Fn (Sh - Qf u) + (1 - t) * Fn (Sh - m) := by
      intro u
      have h := hFconv.2 (mem_univ (Sh - Qf u)) (mem_univ (Sh - m)) ht0.le (by linarith : 0 ≤ 1 - t)
        (by ring)
      simp only [smul_eq_mul] at h
      have e2 : t * (Sh - Qf u) + (1 - t) * (Sh - m) = c - X2 u := by simp only [hX2, hc]; ring
      rw [e2] at h
      exact h
    calc ∫ u in Ioo 0 M, Fn (c - X2 u)
        ≤ ∫ u in Ioo 0 M, (t * Fn (Sh - Qf u) + (1 - t) * Fn (Sh - m)) :=
          setIntegral_mono_on hi1 ((hi2.const_mul t).add (integrableOn_const
            (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) enorm_ne_top))
            measurableSet_Ioo fun u _ => hpt u
      _ = t * (∫ u in Ioo 0 M, Fn (Sh - Qf u)) + (1 - t) * (M * Fn (Sh - m)) := by
          rw [integral_add (hi2.const_mul t) (integrableOn_const
            (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) enorm_ne_top), integral_const_mul,
            setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hM.le, sub_zero]
          ring
  -- Jensen for `F`
  have hstep3 : M * Fn (Sh - m) ≤ ∫ u in Ioo 0 M, Fn (Sh - Qf u) := by
    have hQb2 : ∀ u, |Qf u| ≤ B + B := fun u => (hQb u).trans (by linarith)
    rw [hFint hQm hQb2 Sh, hFeq]
    have hAJ : M * Ahinge ν (Sh - m) ≤ ∫ u in Ioo 0 M, Ahinge ν (Sh - Qf u) := by
      rw [hinge_swap ν hν hQm hQb2 Sh]
      unfold Ahinge
      rw [← integral_const_mul]
      refine integral_mono ((hinge_int ν hν (Sh - m)).const_mul M)
        (hinge_prod_int ν hν hQm hQb2 Sh).integral_prod_right fun ζ => ?_
      have hJ : M * (Sh - m - ζ) = ∫ u in Ioo 0 M, (Sh - ζ - Qf u) := by
        rw [ioo_sub_const le_rfl hM.le le_rfl (Sh - ζ) hint, sub_zero, hm]
        field_simp
        ring
      have hI1 : IntegrableOn (fun u => Sh - ζ - Qf u) (Icc 0 M) volume :=
        (icc_const_int M (Sh - ζ)).sub hint
      have hI2 : IntegrableOn (fun u => max (Sh - ζ - Qf u) 0) (Icc 0 M) volume :=
        hI1.sup (icc_const_int M 0)
      have hle1 : ∫ u in Ioo 0 M, (Sh - ζ - Qf u) ≤ ∫ u in Ioo 0 M, max (Sh - ζ - Qf u) 0 :=
        setIntegral_mono_on (IntegrableOn.mono_set hI1 hsubI) (IntegrableOn.mono_set hI2 hsubI)
          measurableSet_Ioo fun u _ => le_max_left _ _
      have hle2 : 0 ≤ ∫ u in Ioo 0 M, max (Sh - ζ - Qf u) 0 :=
        setIntegral_nonneg measurableSet_Ioo fun u _ => le_max_right _ _
      show M * max (Sh - m - ζ) 0 ≤ ∫ u in Ioo 0 M, max (Sh - ζ - Qf u) 0
      rcases le_total (Sh - m - ζ) 0 with hneg | hpos
      · rw [max_eq_right hneg, mul_zero]; exact hle2
      · rw [max_eq_left hpos, hJ]; exact hle1
    have hlin : ∫ u in Ioo 0 M, Qf u = M * m := by rw [hm]; field_simp
    rw [hlin]
    have hHp : 0 ≤ H + p := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hAJ hHp]
  have hfinal := hstep1.trans hstep2
  nlinarith [mul_le_mul_of_nonneg_left hstep3 (by linarith : 0 ≤ 1 - t)]

end hold


end DFRQ

namespace DFRQ

lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ OWMR.renewalMeasure ρ (Set.Ico 0 w) := by
  unfold OWMR.renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

lemma mirrorAvg_eq (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p s S a : ℝ) :
    OWMR.mirrorAvg ρ h p s S a = OWMR.ssAvgCost ρ (fun y => OWMR.whLoss h p (a - y)) 0 s S := by
  unfold OWMR.mirrorAvg OWMR.ssAvgCost OWMR.ssPeriodCost
  simp only [zero_mul, zero_add]

lemma bdd_of_cont {φ : ℝ → ℝ} (hφ : Continuous φ) (c e : ℝ) :
    ∃ C, ∀ y ∈ Set.Icc c e, φ y ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := c) (b := e)).exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨C, fun y hy => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC y hy)⟩

lemma renewalM_eq (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) :
    OWMR.renewalM ρ w = OWMR.renewalMeasure ρ (Set.Ico 0 w) := by
  unfold OWMR.renewalM OWMR.renewalMeasure
  rw [Measure.sum_apply _ measurableSet_Ico]
  refine tsum_congr fun k => ?_
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ico]
  constructor
  · intro h; exact ⟨Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _, h⟩
  · exact fun h => h.2

lemma integrable_marginal {n : ℕ} (N : OWMR.Network n) (hN : N.Standing) (i : Fin n) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (N.marginal i) := by
  unfold OWMR.Network.marginal
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable]
  have h := integrable_toReal_of_lintegral_ne_top
    (f := fun x : OWMR.DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
    ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
  simpa [Function.comp_def] using h

lemma integrable_sum {n : ℕ} (N : OWMR.Network n) (hN : N.Standing) (i : Fin n) (L : ℕ) :
    Integrable (fun z : Fin L → ℝ≥0 => ∑ j, (z j : ℝ))
      (Measure.pi fun _ : Fin L => N.marginal i) := by
  refine integrable_finsetSum _ fun j _ => ?_
  have hmp := measurePreserving_eval (μ := fun _ : Fin L => N.marginal i) j
  exact (hmp.integrable_comp measurable_coe_nnreal_real.aestronglyMeasurable).2
    (integrable_marginal N hN i)

end DFRQ

open DFRQ in
theorem solution {n : ℕ} (N : OWMR.Network n) (hN : N.Standing) (i : Fin n)
    (wh w t : ℝ) (hw : 0 < w) (hwwh : w ≤ wh) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hM : OWMR.renewalM (N.marginal i) w = ENNReal.ofReal t * OWMR.renewalM (N.marginal i) wh)
    (hconc : ConcaveOn ℝ (Set.Icc 0 wh)
      (fun x => (OWMR.renewalMeasure (N.marginal i) (Set.Icc 0 x)).toReal)) :
    (∀ S Sh : ℝ, OWMR.mirrorCost (N.marginal i) N.h N.p (S - w) S
        ≤ ENNReal.ofReal t * OWMR.mirrorCost (N.marginal i) N.h N.p (Sh - wh) Sh) ∧
    ∀ Sh : ℝ, ∃ S : ℝ, OWMR.ssAvgCost (N.marginal i) (N.F i) 0 (S - w) S
        ≤ OWMR.ssAvgCost (N.marginal i) (N.F i) 0 (Sh - wh) Sh := by
  set ρ := N.marginal i with hρdef
  have hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ := by
    rw [hρdef]; unfold OWMR.Network.marginal
    rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
    exact hN.mean_pos i
  set U := OWMR.renewalMeasure ρ with hUdef
  have hwh : 0 < wh := lt_of_lt_of_le hw hwwh
  have hfin : U (Ico 0 wh) ≠ ∞ := (OWMR.renewalMeasure_Ico_lt_top ρ hρ wh).ne
  have hfin2 : U (Icc 0 wh) ≠ ∞ := ne_top_of_le_ne_top
    (OWMR.renewalMeasure_Ico_lt_top ρ hρ (wh + 1)).ne (measure_mono (Icc_subset_Ico_right (by linarith)))
  set M := Mt U wh with hMdef
  have hM1 : 1 ≤ M := by
    have := ENNReal.toReal_mono hfin (one_le_renewal ρ wh hwh)
    simpa [hMdef, Mt] using this
  have hM0 : 0 < M := by linarith
  have hMw : (U (Ico 0 w)).toReal = t * M := by
    have h := hM
    rw [renewalM_eq, renewalM_eq] at h
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht0.le]
    rfl
  set Qf := Q U wh with hQdef
  have hQmono : Monotone Qf := Q_mono hwh.le hfin
  have hQconv : ConvexOn ℝ (Icc 0 M) Qf := Q_convex hwh.le hfin hfin2 hconc
  have hQb : ∀ u, |Qf u| ≤ wh := fun u =>
    abs_le.2 ⟨by linarith [Q_nonneg hwh.le hfin u], Q_le hwh.le hfin u⟩
  have hT_w : ∀ g : ℝ → ℝ, Measurable g →
      ∫ x in Ico 0 w, g x ∂U = t * ∫ u in Ioo 0 M, g (Qf (t * u)) := by
    intro g hg
    rw [integral_Q hwh.le hfin hw.le hwwh g hg, hMw, integral_scale _ ht0 hM0.le]
  have hT_wh : ∀ g : ℝ → ℝ, Measurable g →
      ∫ x in Ico 0 wh, g x ∂U = ∫ u in Ioo 0 M, g (Qf u) := by
    intro g hg
    rw [integral_Q hwh.le hfin hwh.le le_rfl g hg]
    rfl
  constructor
  · -- mirror contraction
    intro S Sh
    have hhp : 0 < N.h := hN.h_pos
    have hpp : 0 < N.p := hN.p_pos
    set c := Qf (t * (N.h / (N.h + N.p) * M)) with hc
    have hφc : ∀ a : ℝ, Continuous fun y => OWMR.whLoss N.h N.p (a - y) := fun a => by
      unfold OWMR.whLoss; fun_prop
    have hφ0 : ∀ a y : ℝ, 0 ≤ OWMR.whLoss N.h N.p (a - y) := fun a y =>
      add_nonneg (mul_nonneg hhp.le (le_max_right _ _)) (mul_nonneg hpp.le (le_max_right _ _))
    have hloss : ∀ a b x : ℝ, OWMR.whLoss N.h N.p (a - b - (a - x))
        = N.h * max (x - b) 0 + N.p * max (b - x) 0 := by
      intro a b x
      unfold OWMR.whLoss
      rw [show a - b - (a - x) = x - b by ring, show -(x - b) = b - x by ring]
    have hgm : ∀ b : ℝ, Measurable fun x : ℝ => N.h * max (x - b) 0 + N.p * max (b - x) 0 :=
      fun b => by fun_prop
    -- the shortened window at the center `S - c`
    have hL : OWMR.mirrorAvg ρ N.h N.p (S - w) S (S - c)
        = ENNReal.ofReal ((∫ u in Ioo 0 M, (N.h * max (Qf (t * u) - c) 0
            + N.p * max (c - Qf (t * u)) 0)) / M) := by
      rw [mirrorAvg_eq, OWMR.ss_renewal_reward ρ hρ _ (hφc _).measurable (hφ0 _) 0 (S - w) S le_rfl
        (by linarith) (bdd_of_cont (hφc _) _ _), zero_add, show S - (S - w) = w by ring]
      simp_rw [hloss]
      rw [hT_w _ (hgm c), hMw]
      congr 1
      field_simp
    have hR : ∀ a' : ℝ, OWMR.mirrorAvg ρ N.h N.p (Sh - wh) Sh a'
        = ENNReal.ofReal ((∫ u in Ioo 0 M, (N.h * max (Qf u - (Sh - a')) 0
            + N.p * max ((Sh - a') - Qf u) 0)) / M) := by
      intro a'
      rw [mirrorAvg_eq, OWMR.ss_renewal_reward ρ hρ _ (hφc _).measurable (hφ0 _) 0 (Sh - wh) Sh
        le_rfl (by linarith) (bdd_of_cont (hφc _) _ _), zero_add, show Sh - (Sh - wh) = wh by ring]
      have e : ∀ x, OWMR.whLoss N.h N.p (a' - (Sh - x))
          = N.h * max (x - (Sh - a')) 0 + N.p * max ((Sh - a') - x) 0 := by
        intro x
        unfold OWMR.whLoss
        rw [show a' - (Sh - x) = x - (Sh - a') by ring, show -(x - (Sh - a')) = (Sh - a') - x by ring]
      simp_rw [e]
      rw [hT_wh _ (hgm _)]
      rfl
    calc OWMR.mirrorCost ρ N.h N.p (S - w) S ≤ OWMR.mirrorAvg ρ N.h N.p (S - w) S (S - c) :=
          iInf_le (fun a => OWMR.mirrorAvg ρ N.h N.p (S - w) S a) (S - c)
      _ = _ := hL
      _ ≤ ENNReal.ofReal t * OWMR.mirrorCost ρ N.h N.p (Sh - wh) Sh := by
          unfold OWMR.mirrorCost
          rw [ENNReal.mul_iInf_of_ne (by simpa using ht0) ENNReal.ofReal_ne_top]
          refine le_iInf fun a' => ?_
          rw [hR a', ← ENNReal.ofReal_mul ht0.le]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_div_assoc', div_le_div_iff_of_pos_right hM0]
          exact mirror_contract hM0 ht0 ht1 hhp hpp hQmono hQconv (Sh - a')
  · -- holding and backlog contraction
    intro Sh
    have hHi : 0 < N.H i := hN.H_pos i
    have hpp : 0 < N.p := hN.p_pos
    have hsm : Measurable fun z : Fin (N.L i + 1) → ℝ≥0 => ∑ j, (z j : ℝ) :=
      Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real
    set ν := (Measure.pi fun _ : Fin (N.L i + 1) => ρ).map (fun z => ∑ j, (z j : ℝ)) with hνdef
    haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hsm.aemeasurable
    have hν : Integrable id ν := by
      rw [hνdef, integrable_map_measure aestronglyMeasurable_id hsm.aemeasurable]
      exact integrable_sum N hN i (N.L i + 1)
    have hFeq : ∀ y, N.F i y = (N.H i + N.p) * Ahinge ν y - N.p * (y - ∫ ζ, ζ ∂ν) := by
      intro y
      unfold OWMR.Network.F
      have hg : Measurable fun ζ : ℝ => N.H i * max (y - ζ) 0 + N.p * max (ζ - y) 0 := by fun_prop
      have hmap := integral_map (μ := Measure.pi fun _ : Fin (N.L i + 1) => ρ) hsm.aemeasurable
        hg.aestronglyMeasurable
      rw [← hνdef] at hmap
      rw [← hρdef, ← hmap]
      have e : ∀ ζ, N.H i * max (y - ζ) 0 + N.p * max (ζ - y) 0
          = (N.H i + N.p) * max (y - ζ) 0 - N.p * (y - ζ) := by
        intro ζ
        rcases le_total (y - ζ) 0 with h1 | h1
        · rw [max_eq_right h1, max_eq_left (by linarith)]; ring
        · rw [max_eq_left h1, max_eq_right (by linarith)]; ring
      simp_rw [e]
      unfold Ahinge
      have hid : Integrable (fun ζ : ℝ => ζ) ν := hν
      have hi1 : Integrable (fun ζ : ℝ => (N.H i + N.p) * max (y - ζ) 0) ν :=
        (hinge_int ν hν y).const_mul _
      have hi3 : Integrable (fun ζ : ℝ => y - ζ) ν := (integrable_const y).sub hid
      have hi2 : Integrable (fun ζ : ℝ => N.p * (y - ζ)) ν := hi3.const_mul _
      rw [integral_sub hi1 hi2, integral_const_mul, integral_const_mul,
        integral_sub (integrable_const y) hid, integral_const, smul_eq_mul,
        probReal_univ, one_mul]
    have hFconv : ConvexOn ℝ univ (N.F i) := (OWMR.F_properties N hN i).2.1
    obtain ⟨S, hS⟩ := hold_contract ν hM0 ht0 ht1 hQmono hQconv hQb hν hHi hpp hFeq hFconv Sh
    refine ⟨S, ?_⟩
    have hF := OWMR.F_properties N hN i
    have hFc : Continuous (N.F i) := by
      rw [Metric.continuous_iff]
      intro b ε hε
      refine ⟨ε / (N.H i + N.p + 1), by positivity, fun a hab => ?_⟩
      rw [Real.dist_eq] at hab ⊢
      have h1 := hF.2.2.1 a b
      have hpos : 0 < N.H i + N.p + 1 := by linarith
      calc |N.F i a - N.F i b| ≤ (N.H i + N.p) * |a - b| := h1
        _ ≤ (N.H i + N.p) * (ε / (N.H i + N.p + 1)) :=
            mul_le_mul_of_nonneg_left hab.le (by linarith)
        _ < ε := by
            rw [mul_div_assoc', div_lt_iff₀ hpos]
            nlinarith
    have hFm : ∀ a : ℝ, Measurable fun x => N.F i (a - x) := fun a =>
      hFc.measurable.comp (measurable_const.sub measurable_id)
    rw [OWMR.ss_renewal_reward ρ hρ _ hFc.measurable hF.1 0 (S - w) S le_rfl (by linarith)
        (bdd_of_cont hFc _ _), OWMR.ss_renewal_reward ρ hρ _ hFc.measurable hF.1 0 (Sh - wh) Sh
        le_rfl (by linarith) (bdd_of_cont hFc _ _), zero_add, zero_add,
      show S - (S - w) = w by ring, show Sh - (Sh - wh) = wh by ring, hT_w _ (hFm S),
      hT_wh _ (hFm Sh), hMw]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_mul_left _ _ ht0.ne']
    exact div_le_div_of_nonneg_right hS hM0.le
