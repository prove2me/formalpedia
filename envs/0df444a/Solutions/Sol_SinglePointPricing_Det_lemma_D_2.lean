-- Prove2me | solution 1 for SinglePointPricing.Det.lemma_D_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:16:30.301632+00:00
-- url     : https://prove2.me/submissions/1ea3b7ea-fa30-4a28-8ec4-63d8bcc756ff

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase
import Theorems.Thm_SinglePointPricing_Det_theorem_1
import Theorems.Thm_SinglePointPricing_Det_lemma_C_2
import Theorems.Thm_SinglePointPricing_Det_propD1_worst_terms

namespace SPPL2
open SinglePointPricing.Det MeasureTheory

lemma GA_pos (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) : 0 < GammaA α x := by
  unfold GammaA
  split_ifs with h
  · exact Real.exp_pos _
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply Real.rpow_pos_of_pos; nlinarith

lemma GA_zero (α : ℝ) : GammaA α 0 = 1 := by
  unfold GammaA; split_ifs <;> simp

lemma GAInv_GA (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    GammaAInv α (GammaA α x) = x := by
  unfold GammaA GammaAInv
  split_ifs with h
  · simp
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    have hb : 0 ≤ 1 + (1 - α) * x := by nlinarith
    rw [← Real.rpow_mul hb]
    have : -(1 / (1 - α)) * -(1 - α) = 1 := by field_simp
    rw [this, Real.rpow_one]; field_simp; ring

lemma GAInv_pos (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    0 < GammaAInv α q := by
  rcases hq with ⟨h0, h1⟩
  unfold GammaAInv
  split_ifs with h
  · have := Real.log_neg h0 h1; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply div_pos _ ha
    have : 1 < q ^ (-(1 - α)) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (by linarith)
    linarith

lemma GAInv_anti (α x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 < x) (hxy : x < y) :
    GammaAInv α y < GammaAInv α x := by
  unfold GammaAInv
  split_ifs with h
  · have := Real.log_lt_log hx hxy; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply div_lt_div_of_pos_right _ ha
    have := Real.rpow_lt_rpow_of_neg hx hxy (by linarith : -(1 - α) < 0)
    linarith

lemma one_add_kc (α q : ℝ) (hq : 0 < q) :
    1 + (1 - α) * GammaAInv α q = q ^ (α - 1) := by
  unfold GammaAInv
  split_ifs with h
  · subst h; simp
  · have ha : (1 - α) ≠ 0 := by intro h'; apply h; linarith
    have : -(1 - α) = α - 1 := by ring
    rw [this]; field_simp; ring

lemma log_GA (α v : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hv : 0 ≤ v) (hα1 : α ≠ 1) :
    Real.log (GammaA α v) = -(1 / (1 - α)) * Real.log (1 + (1 - α) * v) := by
  have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 hα1)
  unfold GammaA; rw [if_neg hα1, Real.log_rpow (by nlinarith)]

lemma logGA_tangent (α v v0 : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hv : 0 ≤ v) (hv0 : 0 ≤ v0) :
    Real.log (GammaA α v0) - (v - v0) / (1 + (1 - α) * v0) ≤ Real.log (GammaA α v) := by
  by_cases h1 : α = 1
  · subst h1; unfold GammaA; simp
  · have hk : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    rw [log_GA α v hα hv h1, log_GA α v0 hα hv0 h1]
    have hx : 0 < 1 + (1 - α) * v := by nlinarith
    have hy : 0 < 1 + (1 - α) * v0 := by nlinarith
    have hl := Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [Real.log_div hx.ne' hy.ne'] at hl
    have e1 : (1 + (1 - α) * v) / (1 + (1 - α) * v0) - 1
        = (1 - α) * ((v - v0) / (1 + (1 - α) * v0)) := by field_simp; ring
    rw [e1] at hl
    set t := (v - v0) / (1 + (1 - α) * v0)
    have e : 1 / (1 - α) * (Real.log (1 + (1 - α) * v) - Real.log (1 + (1 - α) * v0)) ≤ t := by
      rw [one_div, inv_mul_le_iff₀ hk]; linarith
    nlinarith

lemma Fbar_lt (α q r p : ℝ) (hr1 : r < 1) (hrp : r ≤ p) (hp1 : p ≤ 1) :
    Fbar α 1 q r p = GammaA α (GammaAInv α q * (p - r) / (1 - r)) := by
  simp [Fbar, hr1, Gbar, not_lt.mpr hrp, hp1]

lemma Fbar_ge (α q r p : ℝ) (hr1 : 1 ≤ r) (hp0 : 0 ≤ p) (hpr : p ≤ r) :
    Fbar α 1 q r p = GammaA α (GammaAInv α q * p) := by
  simp [Fbar, not_lt.mpr hr1, Gbar, not_lt.mpr hp0, hpr]

lemma optFun_of_max (F : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hmax : IsMaxOn (fun v => v * F v) (Set.Ici 0) r) : optFun F = r * F r := by
  unfold optFun
  apply IsGreatest.csSup_eq
  refine ⟨⟨r, hr, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hmax hv

lemma optFun_r (α q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hr : r ∈ rSet α 1 q) : optFun (Fbar α 1 q r) = r * Fbar α 1 q r r := by
  obtain ⟨h0, hmax⟩ := lemma_C_2 α 1 q r hα one_pos hq hr
  exact optFun_of_max _ r h0 hmax

lemma rLow_eq (α q : ℝ) : rLow α 1 q = 1 / (GammaAInv α q + 1) := rfl

lemma GA0 (x : ℝ) : GammaA 0 x = (1 + x)⁻¹ := by
  unfold GammaA; norm_num; rw [Real.rpow_neg_one]

lemma GA1 (x : ℝ) : GammaA 1 x = Real.exp (-x) := by
  unfold GammaA; norm_num


lemma rLow_eqw (α w q : ℝ) : rLow α w q = w / (GammaAInv α q + 1) := rfl

lemma GA_GAInv (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : 0 < q) :
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

lemma GAInv_one (α : ℝ) : GammaAInv α 1 = 0 := by
  unfold GammaAInv; split_ifs <;> simp

lemma Fbar_scale (α w q r x : ℝ) (hw : 0 < w) :
    Fbar α w q r (w * x) = Fbar α 1 q (r / w) x := by
  have hw' : w ≠ 0 := hw.ne'
  unfold Fbar Gbar
  by_cases hrw : r < w
  · have h1 : r / w < 1 := by rw [div_lt_one hw]; exact hrw
    rw [if_pos hrw, if_pos h1]
    by_cases hx : x < r / w
    · have : w * x < r := by rw [lt_div_iff₀ hw] at hx; linarith
      rw [if_pos this, if_pos hx]
      simp [GAInv_one]
    · have : ¬ (w * x < r) := by rw [lt_div_iff₀ hw] at hx; intro h; apply hx; linarith
      rw [if_neg this, if_neg hx]
      by_cases hx1 : x ≤ 1
      · have : w * x ≤ w := by nlinarith
        rw [if_pos this, if_pos hx1]
        congr 2
        have : w - r ≠ 0 := by linarith
        have : 1 - r / w ≠ 0 := by linarith
        field_simp
      · have : ¬ (w * x ≤ w) := by intro h; apply hx1; nlinarith
        rw [if_neg this, if_neg hx1]
  · have h1 : ¬ (r / w < 1) := by rw [div_lt_one hw]; exact hrw
    rw [if_neg hrw, if_neg h1]
    by_cases hx : x < 0
    · have : w * x < 0 := by nlinarith
      rw [if_pos this, if_pos hx]
      simp [GAInv_one]
    · have : ¬ (w * x < 0) := by intro h; apply hx; nlinarith
      rw [if_neg this, if_neg hx]
      by_cases hx1 : x ≤ r / w
      · have : w * x ≤ r := by rw [le_div_iff₀ hw] at hx1; linarith
        rw [if_pos this, if_pos hx1]
        congr 2
        field_simp
        ring
      · have : ¬ (w * x ≤ r) := by rw [le_div_iff₀ hw] at hx1; intro h; apply hx1; linarith
        rw [if_neg this, if_neg hx1]

lemma rSet_scale (α w q r : ℝ) (hw : 0 < w) (hc : 0 < GammaAInv α q) :
    r ∈ rSet α w q ↔ r / w ∈ rSet α 1 q := by
  unfold rSet
  simp only [Set.mem_union, Set.mem_Ico, Set.mem_setOf_eq, rLow_eqw]
  have e1 : w / (GammaAInv α q + 1) ≤ r ↔ 1 / (GammaAInv α q + 1) ≤ r / w := by
    rw [div_le_iff₀ (by linarith), div_le_div_iff₀ (by linarith) hw]; constructor <;> intro h <;> linarith
  have e2 : r < w ↔ r / w < 1 := by rw [div_lt_one hw]
  have e3 : w ≤ r ↔ 1 ≤ r / w := by rw [le_div_iff₀ hw, one_mul]
  have e4 : α * GammaAInv α q * r ≤ w ↔ α * GammaAInv α q * (r / w) ≤ 1 := by
    rw [show α * GammaAInv α q * (r / w) = (α * GammaAInv α q * r) / w by ring, div_le_one hw]
  rw [e1, e2, e3, e4]

lemma optFun_rw (α w q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ rSet α w q) :
    optFun (Fbar α w q r) = r * Fbar α w q r r := by
  obtain ⟨h0, hmax⟩ := lemma_C_2 α w q r hα hw hq hr
  exact optFun_of_max _ r h0 hmax

lemma optFun_scale (α w q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ rSet α w q) :
    optFun (Fbar α w q r) = w * optFun (Fbar α 1 q (r / w)) := by
  have hr' := (rSet_scale α w q r hw (GAInv_pos α q hα hq)).mp hr
  rw [optFun_rw α w q r hα hw hq hr, optFun_rw α 1 q (r / w) hα one_pos hq hr',
    ← Fbar_scale α w q r (r / w) hw]
  have : w * (r / w) = r := by field_simp
  rw [this]; field_simp

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

lemma dirac_isMech (p : ℝ) (hp : 0 ≤ p) : IsMech (Measure.dirac p) := by
  refine ⟨inferInstance, ?_⟩
  simp [Measure.dirac_apply', hp.not_gt]

lemma dirac_mem_Pd (p : ℝ) (hp : 0 ≤ p) : Measure.dirac p ∈ Pd := by
  unfold Pd; exact ⟨p, hp, rfl⟩

lemma ratio_nonneg (p : ℝ) (hp : 0 ≤ p) (μ : Measure ℝ) : 0 ≤ ratio (Measure.dirac p) μ := by
  rw [ratio_dirac]
  apply div_nonneg (mul_nonneg hp ENNReal.toReal_nonneg)
  unfold opt
  apply Real.sSup_nonneg
  rintro _ ⟨v, hv, rfl⟩
  exact mul_nonneg hv ENNReal.toReal_nonneg

lemma inner_eq_S (α w q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hp : 0 ≤ p) :
    sInf (ratio (Measure.dirac p) '' FClass α w q) =
      sInf (ratio (Measure.dirac p) '' SFamily α w q) := by
  have h1 := theorem_1 α hα w hw q hq {Measure.dirac p} (by
    rintro Ψ hΨ; rw [Set.mem_singleton_iff] at hΨ; subst hΨ; exact dirac_isMech p hp)
  unfold maximin at h1
  simpa only [Set.image_singleton, csSup_singleton] using h1

lemma S_ratio (α w q x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hx : 0 ≤ x) (ν : Measure ℝ) (hν : ν ∈ SFamily α w q) :
    ∃ r' ∈ rSet α 1 q, ratio (Measure.dirac (w * x)) ν =
      x * Fbar α 1 q r' x / optFun (Fbar α 1 q r') := by
  obtain ⟨_, _, r, hr, htail⟩ := hν
  refine ⟨r / w, (rSet_scale α w q r hw (GAInv_pos α q hα hq)).mp hr, ?_⟩
  rw [ratio_dirac, opt_eq_optFun ν _ htail, htail (w * x) (by positivity), Fbar_scale α w q r x hw,
    optFun_scale α w q r hα hw hq hr]
  rw [mul_assoc, mul_div_mul_left _ _ hw.ne']

lemma inner_ge (α w q x V : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hx : 0 ≤ x) (hS : (SFamily α w q).Nonempty)
    (hlow : ∀ r' ∈ rSet α 1 q, V ≤ x * Fbar α 1 q r' x / optFun (Fbar α 1 q r')) :
    V ≤ sInf (ratio (Measure.dirac (w * x)) '' FClass α w q) := by
  rw [inner_eq_S α w q (w * x) hα hw hq (by positivity)]
  apply le_csInf (hS.image _)
  rintro _ ⟨ν, hν, rfl⟩
  obtain ⟨r', hr', he⟩ := S_ratio α w q x hα hw hq hx ν hν
  rw [he]; exact hlow r' hr'

lemma ratio_le_one (α w q γ : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hγ : 0 ≤ γ) (ν : Measure ℝ) (hν : ν ∈ SFamily α w q) :
    ratio (Measure.dirac γ) ν ≤ 1 := by
  obtain ⟨_, _, r, hr, htail⟩ := hν
  obtain ⟨h0, hmax⟩ := lemma_C_2 α w q r hα hw hq hr
  rw [ratio_dirac, opt_eq_optFun ν _ htail, htail γ hγ, optFun_of_max _ r h0 hmax]
  have h1 : γ * Fbar α w q r γ ≤ r * Fbar α w q r r := hmax hγ
  have h2 : 0 ≤ γ * Fbar α w q r γ := by
    rw [← htail γ hγ]; exact mul_nonneg hγ ENNReal.toReal_nonneg
  exact div_le_one_of_le₀ h1 (le_trans h2 h1)

lemma S_nonempty (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hpos : 0 < maximin Pd (FClass α w q)) :
    (SFamily α w q).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h1 := theorem_1 α hα w hw q hq Pd (by rintro Ψ ⟨γ, hγ, rfl⟩; exact dirac_isMech γ hγ)
  rw [h1, hne] at hpos
  unfold maximin at hpos
  simp only [Set.image_empty, Real.sInf_empty] at hpos
  have : (fun _ : Measure ℝ => (0 : ℝ)) '' Pd = {0} :=
    Set.Nonempty.image_const ⟨Measure.dirac 0, (dirac_mem_Pd 0 le_rfl)⟩ 0
  rw [this, csSup_singleton] at hpos
  exact lt_irrefl _ hpos

lemma inner_le (α w q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hp : 0 ≤ p) (hS : (SFamily α w q).Nonempty) :
    sInf (ratio (Measure.dirac p) '' FClass α w q) ≤ maximin Pd (FClass α w q) := by
  unfold maximin
  refine le_csSup ?_ (Set.mem_image_of_mem _ (dirac_mem_Pd p hp))
  refine ⟨1, ?_⟩
  rintro _ ⟨Ψ, ⟨γ, hγ, rfl⟩, rfl⟩
  dsimp only
  rw [inner_eq_S α w q γ hα hw hq hγ]
  obtain ⟨ν, hν⟩ := hS
  refine le_trans (csInf_le ⟨0, ?_⟩ ⟨ν, hν, rfl⟩) (ratio_le_one α w q γ hα hw hq hγ ν hν)
  rintro _ ⟨μ, _, rfl⟩; exact ratio_nonneg γ hγ μ

lemma R2_eq (p : ℝ) (hp : p ≤ 1) : R2 p = p := by
  simp [R2, sf, Measure.dirac_apply', hp]

lemma Fbar_below (α q r x : ℝ) (hr1 : r < 1) (hxr : x ≤ r) : Fbar α 1 q r x = 1 := by
  by_cases h : x < r
  · simp [Fbar, hr1, Gbar, h, GAInv_one, GA_zero]
  · have : x = r := le_antisymm hxr (not_lt.mp h)
    subst this
    simp [Fbar, hr1, Gbar, hr1.le, GA_zero]

lemma optFun_lt (α q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hr : r ∈ Set.Ico (rLow α 1 q) 1) : optFun (Fbar α 1 q r) = r := by
  rw [optFun_rw α 1 q r hα one_pos hq (Or.inl hr), Fbar_below α q r r hr.2 le_rfl, mul_one]

lemma rLow_pos (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    0 < rLow α 1 q := by
  have := GAInv_pos α q hα hq; rw [rLow_eqw]; positivity

lemma rLow_pos_lt1 (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    rLow α 1 q < 1 := by
  have := GAInv_pos α q hα hq; rw [rLow_eqw, div_lt_one (by linarith)]; linarith

lemma no_high (α q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hqL : q < qLow α) (hr1 : 1 ≤ r) (hr2 : α * GammaAInv α q * r ≤ 1) : False := by
  by_cases hα0 : α = 0
  · subst hα0; simp [qLow] at hqL; linarith [hq.1]
  · have hαp : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hα0)
    have hqL' : q < GammaA α (1 / α) := by simpa [qLow, hα0] using hqL
    have := GAInv_anti α _ _ hα hq.1 hqL'
    rw [GAInv_GA α _ hα (by positivity)] at this
    have h3 : 1 < α * GammaAInv α q := by rw [div_lt_iff₀ hαp] at this; linarith
    nlinarith

lemma lowbound (α q x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Ico (rLow α 1 q) 1) (r' : ℝ) (hr' : r' ∈ rSet α 1 q) :
    (qLow α ≤ q → min (R1 α q x) (min (R2 x) (R3 α q x)) ≤
      x * Fbar α 1 q r' x / optFun (Fbar α 1 q r')) ∧
    (q < qLow α → min (R1 α q x) (R2 x) ≤ x * Fbar α 1 q r' x / optFun (Fbar α 1 q r')) := by
  have D := propD1_worst_terms α hα q hq
  have hL := rLow_pos α q hα hq
  have hx0 : 0 ≤ x := le_trans hL.le hx.1
  rcases hr' with hr' | ⟨hr1, hr2⟩
  · rw [optFun_lt α q r' hα hq hr']
    have hr0 : 0 < r' := lt_of_lt_of_le hL hr'.1
    by_cases hrx : r' < x
    · have hb : R1 α q x ≤ x * Fbar α 1 q r' x / r' :=
        (D.1 x ⟨lt_of_le_of_lt hr'.1 hrx, hx.2⟩).2 ⟨r', ⟨hr'.1, hrx⟩, rfl⟩
      exact ⟨fun _ => le_trans (min_le_left _ _) hb, fun _ => le_trans (min_le_left _ _) hb⟩
    · have hxr : x ≤ r' := not_lt.mp hrx
      rw [Fbar_below α q r' x hr'.2 hxr, mul_one]
      have hb : R2 x ≤ x / r' := by
        rw [R2_eq x hx.2.le, le_div_iff₀ hr0]
        nlinarith [hr'.2]
      exact ⟨fun _ => le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hb),
        fun _ => le_trans (min_le_right _ _) hb⟩
  · refine ⟨fun hqL => ?_, fun hqL => (no_high α q r' hα hq hqL hr1 hr2).elim⟩
    have hb := (D.2 hqL x ⟨hx0, hx.2.le⟩).1 ⟨r', ⟨hr1, hr2⟩, rfl⟩
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) hb)

lemma lowbound_one (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hqL : qLow α ≤ q) (r' : ℝ) (hr' : r' ∈ rSet α 1 q) :
    min q (R3 α q 1) ≤ 1 * Fbar α 1 q r' 1 / optFun (Fbar α 1 q r') := by
  have D := propD1_worst_terms α hα q hq
  have hL := rLow_pos α q hα hq
  rcases hr' with hr' | ⟨hr1, hr2⟩
  · rw [optFun_lt α q r' hα hq hr', Fbar_lt α q r' 1 hr'.2 hr'.2.le le_rfl]
    have hr0 : 0 < r' := lt_of_lt_of_le hL hr'.1
    have : GammaAInv α q * (1 - r') / (1 - r') = GammaAInv α q := by
      have : 1 - r' ≠ 0 := by linarith [hr'.2]
      field_simp
    rw [this, GA_GAInv α q hα hq.1, one_mul]
    have : q ≤ q / r' := by rw [le_div_iff₀ hr0]; nlinarith [hr'.2, hq.1]
    exact le_trans (min_le_left _ _) this
  · have hb := (D.2 hqL 1 ⟨zero_le_one, le_rfl⟩).1 ⟨r', ⟨hr1, hr2⟩, rfl⟩
    exact le_trans (min_le_right _ _) hb

lemma c0 (q : ℝ) : GammaAInv 0 q = 1 / q - 1 := by
  unfold GammaAInv; norm_num; rw [Real.rpow_neg_one]

lemma rLow0 (q : ℝ) (hq : 0 < q) : rLow 0 1 q = q := by
  rw [rLow_eqw, c0]; field_simp; ring

lemma GV0 : GammaA 0 (vTilde 0) = 1 / 2 := by
  simp [vTilde, GA0]; norm_num

lemma qLow0 : qLow 0 = 0 := by simp [qLow]

lemma R3_0 (q p : ℝ) : R3 0 q p = GammaAInv 0 q * p / (1 + GammaAInv 0 q * p) := by
  simp [R3, vTilde, GA0]; ring

lemma R3_0_mono (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) : MonotoneOn (R3 0 q) (Set.Icc 0 1) := by
  have hc := GAInv_pos 0 q ⟨le_rfl, zero_le_one⟩ hq
  intro x hx y hy hxy
  rw [R3_0, R3_0, div_le_div_iff₀ (by nlinarith [hx.1]) (by nlinarith [hy.1])]
  nlinarith [mul_le_mul_of_nonneg_left hxy hc.le]

lemma R3_0_cont (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousWithinAt (R3 0 q) (Set.Icc 0 1) 1 := by
  have hc := GAInv_pos 0 q ⟨le_rfl, zero_le_one⟩ hq
  have : R3 0 q = fun p => GammaAInv 0 q * p / (1 + GammaAInv 0 q * p) := funext (R3_0 q)
  rw [this]
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  nlinarith

lemma GA_anti (α x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) (hxy : x ≤ y) :
    GammaA α y ≤ GammaA α x := by
  unfold GammaA
  split_ifs with h
  · exact Real.exp_le_exp.mpr (by linarith)
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith)
    have : 0 < 1 / (1 - α) := by positivity
    linarith

lemma mu_at_rLow (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    muAQ α q (rLow α 1 q) = rLow α 1 q := by
  have hc := GAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  have ha_eq := one_add_kc α q hq.1
  rw [← hc_def] at ha_eq
  set a := q ^ (α - 1) with ha_def
  have hapos : 0 < a := by rw [← ha_eq]; nlinarith [hα.2]
  have hr : rLow α 1 q = 1 / (c + 1) := by rw [rLow_eqw, ← hc_def]
  rw [hr]
  set s0 := c / (c + 1) with hs0
  have h1p : 1 - 1 / (c + 1) = s0 := by rw [hs0]; field_simp; ring
  have hs0pos : 0 < s0 := by positivity
  have hDelta : Delta α q (1 / (c + 1)) = (2 * a * s0 + α * c * s0) ^ 2 := by
    simp only [Delta, ← hc_def, ← ha_def]
    rw [h1p]
    have : a * s0 + α * c * s0 = c := by
      rw [← ha_eq, hs0]; field_simp; ring
    nlinarith [this]
  have hS : Real.sqrt (Delta α q (1 / (c + 1))) = 2 * a * s0 + α * c * s0 := by
    rw [hDelta, Real.sqrt_sq]
    have := hα.1; positivity
  unfold muAQ
  rw [hS, ← hc_def, ← ha_def, h1p]
  have : (2 * a * s0 + α * c * s0 - α * c * s0) / (2 * a) = s0 := by field_simp; ring
  rw [this, ← h1p]; ring

lemma R1_at_rLow (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    R1 α q (rLow α 1 q) = 1 := by
  have hL := rLow_pos α q hα hq
  have hL1 := rLow_pos_lt1 α q hα hq
  unfold R1
  rw [mu_at_rLow α q hα hq, optFun_lt α q _ hα hq ⟨le_rfl, hL1⟩, Fbar_below α q _ _ hL1 le_rfl,
    mul_one, div_self hL.ne']

lemma R1_ge (α q x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Ioo (rLow α 1 q) 1) : x * q ≤ R1 α q x := by
  obtain ⟨⟨r, hr, hEq⟩, _⟩ := (propD1_worst_terms α hα q hq).1 x hx
  rw [← hEq]
  simp only
  have hL := rLow_pos α q hα hq
  have hr0 : 0 < r := lt_of_lt_of_le hL hr.1
  have hr1 : r < 1 := lt_trans hr.2 hx.2
  have hc := GAInv_pos α q hα hq
  rw [Fbar_lt α q r x hr1 hr.2.le hx.2.le]
  have hG : q ≤ GammaA α (GammaAInv α q * (x - r) / (1 - r)) := by
    have h1 : GammaAInv α q * (x - r) / (1 - r) ≤ GammaAInv α q := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [hx.2]
    have := GA_anti α _ _ hα (div_nonneg (mul_nonneg hc.le (by linarith [hr.2])) (by linarith)) h1
    rwa [GA_GAInv α q hα hq.1] at this
  have hx0 : 0 < x := lt_trans hL hx.1
  rw [le_div_iff₀ hr0]
  nlinarith [mul_le_mul_of_nonneg_left hG hx0.le, mul_le_mul_of_nonneg_left hr1.le (mul_pos hx0 hq.1).le]

/-- monotonicity of the revenue `x ↦ x Γ_α(c x)` below `1/(α c)`. -/
lemma xG_mono (α c x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hc : 0 < c) (hx : 0 ≤ x)
    (hxy : x ≤ y) (hy : α * c * y ≤ 1) : x * GammaA α (c * x) ≤ y * GammaA α (c * y) := by
  rcases eq_or_lt_of_le hx with h0 | h0
  · rw [← h0]; simp; exact mul_nonneg (by linarith) (GA_pos α _ hα (by nlinarith)).le
  have hy0 : 0 < y := lt_of_lt_of_le h0 hxy
  have h1 := GA_pos α (c * x) hα (by positivity)
  have h2 := GA_pos α (c * y) hα (by positivity)
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul h0.ne' h1.ne',
    Real.log_mul hy0.ne' h2.ne']
  set t := x / y with ht
  have ht0 : 0 < t := div_pos h0 hy0
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hy0]; exact hxy
  have hxt : x = t * y := by rw [ht]; field_simp
  have hlogt : Real.log x - Real.log y = Real.log t := by
    rw [ht, Real.log_div h0.ne' hy0.ne']
  by_cases h1α : α = 1
  · subst h1α
    rw [GA1, GA1, Real.log_exp, Real.log_exp]
    have := Real.log_le_sub_one_of_pos ht0
    have hcy : c * y ≤ 1 := by linarith
    have : (t - 1) ≤ c * y * (t - 1) := by nlinarith
    have e : c * x = c * y * t := by rw [hxt]; ring
    rw [e]; nlinarith
  · have hk : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1α)
    rw [log_GA α _ hα (by positivity) h1α, log_GA α _ hα (by positivity) h1α]
    have hX : 0 < 1 + (1 - α) * (c * x) := by
      have := mul_nonneg hk.le (mul_nonneg hc.le hx); linarith
    have hY : 0 < 1 + (1 - α) * (c * y) := by
      have := mul_nonneg hk.le (mul_nonneg hc.le hy0.le); linarith
    have hber := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hk.le
      (by linarith [hα.1])
    rw [show 1 + (t - 1) = t by ring] at hber
    have hpos : 0 < t ^ (1 - α) := Real.rpow_pos_of_pos ht0 _
    have hb2 : 1 + (1 - α) * (t - 1) ≤ (1 + (1 - α) * (c * x)) / (1 + (1 - α) * (c * y)) := by
      rw [le_div_iff₀ hY, hxt]
      have : 0 ≤ (1 - α) * (1 - t) * (1 - α * c * y) :=
        mul_nonneg (mul_nonneg hk.le (by linarith)) (by linarith)
      nlinarith
    have hl := Real.log_le_log hpos (le_trans hber hb2)
    rw [Real.log_rpow ht0, Real.log_div hX.ne' hY.ne'] at hl
    have e : 1 / (1 - α) * ((1 - α) * Real.log t) = Real.log t := by field_simp
    have hl2 : Real.log t ≤ 1 / (1 - α) *
        (Real.log (1 + (1 - α) * (c * x)) - Real.log (1 + (1 - α) * (c * y))) := by
      rw [← e]; exact mul_le_mul_of_nonneg_left hl (by positivity)
    nlinarith

lemma R3_form (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hα0 : α ≠ 0) (hqL : qLow α ≤ q) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    1 ≤ 1 / (α * GammaAInv α q) ∧
    R3 α q p = p * GammaA α (GammaAInv α q * p) /
      (1 / (α * GammaAInv α q) * GammaA α (GammaAInv α q * (1 / (α * GammaAInv α q)))) := by
  have hc := GAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  have hαp : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hα0)
  have hac : α * c ≤ 1 := by
    have hqL' : GammaA α (1 / α) ≤ q := by simpa [qLow, hα0] using hqL
    have hc1 : c ≤ 1 / α := by
      rcases eq_or_lt_of_le hqL' with h | h
      · rw [hc_def, ← h, GAInv_GA α _ hα (by positivity)]
      · have := GAInv_anti α _ _ hα (GA_pos α _ hα (by positivity)) h
        rw [GAInv_GA α _ hα (by positivity)] at this
        exact this.le
    rw [le_div_iff₀ hαp] at hc1; linarith
  have hrb1 : 1 ≤ 1 / (α * c) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hrb2 : α * c * (1 / (α * c)) ≤ 1 := by rw [mul_one_div_cancel (by positivity)]
  refine ⟨hrb1, ?_⟩
  have hR3 : R3 α q p = p * Fbar α 1 q (1 / (α * c)) p / optFun (Fbar α 1 q (1 / (α * c))) := by
    simp [R3, hα0, ← hc_def]
  rw [hR3, optFun_rw α 1 q _ hα one_pos hq (Or.inr ⟨hrb1, hrb2⟩),
    Fbar_ge α q _ p hrb1 hp.1 (le_trans hp.2 hrb1), Fbar_ge α q _ _ hrb1 (by linarith) le_rfl,
    ← hc_def]

lemma R3_mono (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hqL : qLow α ≤ q) : MonotoneOn (R3 α q) (Set.Icc 0 1) := by
  by_cases hα0 : α = 0
  · subst hα0; exact R3_0_mono q hq
  have hc := GAInv_pos α q hα hq
  intro x hx y hy hxy
  obtain ⟨hrb1, hx3⟩ := R3_form α q x hα hq hα0 hqL hx
  obtain ⟨_, hy3⟩ := R3_form α q y hα hq hα0 hqL hy
  rw [hx3, hy3]
  have hαp : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hα0)
  have hK : 0 < 1 / (α * GammaAInv α q) *
      GammaA α (GammaAInv α q * (1 / (α * GammaAInv α q))) :=
    mul_pos (by positivity) (GA_pos α _ hα (by positivity))
  apply div_le_div_of_nonneg_right _ hK.le
  apply xG_mono α _ x y hα hc hx.1 hxy
  have : α * GammaAInv α q ≤ 1 := by
    have := hrb1; rw [le_div_iff₀ (by positivity)] at this; linarith
  have hac0 : 0 ≤ α * GammaAInv α q := mul_nonneg hα.1 hc.le
  nlinarith [mul_le_mul_of_nonneg_left hy.2 hac0]

lemma GA_contAt (α c : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hc : 0 ≤ c) :
    ContinuousAt (fun p => GammaA α (c * p)) 1 := by
  by_cases h1 : α = 1
  · subst h1; simp only [GA1]; fun_prop
  · have hk : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    simp only [GammaA, if_neg h1]
    apply ContinuousAt.rpow_const (by fun_prop)
    left; nlinarith

lemma R3_cont (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hqL : qLow α ≤ q) : ContinuousWithinAt (R3 α q) (Set.Icc 0 1) 1 := by
  by_cases hα0 : α = 0
  · subst hα0; exact R3_0_cont q hq
  have hc := GAInv_pos α q hα hq
  set K := 1 / (α * GammaAInv α q) * GammaA α (GammaAInv α q * (1 / (α * GammaAInv α q)))
  have hf : ContinuousAt (fun p => p * GammaA α (GammaAInv α q * p) / K) 1 :=
    (continuousAt_id.mul (GA_contAt α _ hα hc.le)).div_const K
  exact hf.continuousWithinAt.congr (fun p hp => (R3_form α q p hα hq hα0 hqL hp).2)
    (R3_form α q 1 hα hq hα0 hqL ⟨zero_le_one, le_rfl⟩).2

lemma isGLB_div_image_Ico (a w p : ℝ) (ha : 0 < a) (haw : a < w) (hp : 0 ≤ p) :
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

lemma lemA (α β r v : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hr : 0 < r) (hβ : 1 ≤ β * r)
    (hv : r ≤ v) : v * GammaA α (β * (v - r)) ≤ r := by
  have hβ0 : 0 < β := by
    by_contra h; push Not at h; nlinarith
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


noncomputable def nu (α q y : ℝ) : ℝ :=
  1 - q ^ (α - 1) * (1 - y) ^ 2 / (GammaAInv α q * (1 - α * (1 - y)))

lemma mu_root (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (rLow α 1 q) 1) :
    0 ≤ 1 - muAQ α q p ∧ 1 - muAQ α q p ≤ GammaAInv α q / (GammaAInv α q + 1) ∧
      q ^ (α - 1) * (1 - muAQ α q p) ^ 2 + α * GammaAInv α q * (1 - p) * (1 - muAQ α q p)
        - GammaAInv α q * (1 - p) = 0 := by
  have hc := GAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  have ha_eq := one_add_kc α q hq.1
  rw [← hc_def] at ha_eq
  set a := q ^ (α - 1) with ha_def
  have hapos : 0 < a := by rw [← ha_eq]; nlinarith [hα.2]
  have hp1 : 0 ≤ 1 - p := by linarith [hp.2]
  have hpl : 1 ≤ p * (c + 1) := by
    have h := hp.1; rw [rLow_eq, div_le_iff₀ (by linarith)] at h; linarith
  set b := α * c * (1 - p) with hb_def
  set d := c * (1 - p) with hd_def
  have hb0 : 0 ≤ b := by have := hα.1; positivity
  have hd0 : 0 ≤ d := by positivity
  have hDelta : Delta α q p = b ^ 2 + 4 * d * a := by
    simp only [Delta, hb_def, hd_def, ← hc_def, ha_def]; ring
  have hD0 : 0 ≤ Delta α q p := by rw [hDelta]; positivity
  set S := Real.sqrt (Delta α q p) with hS_def
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = b ^ 2 + 4 * d * a := by rw [hS_def, Real.sq_sqrt hD0, hDelta]
  have hmu : muAQ α q p = 1 - (S - b) / (2 * a) := by
    simp only [muAQ, hS_def, hb_def, ← hc_def, ha_def]
  set s := (S - b) / (2 * a) with hs_def
  have hs2 : 2 * a * s = S - b := by rw [hs_def]; field_simp
  have hquad : a * s ^ 2 + b * s - d = 0 := by
    have h4 : 4 * a * (a * s ^ 2 + b * s - d) = 0 := by
      have hSe : S = 2 * a * s + b := by linarith
      rw [hSe] at hS2; linear_combination hS2
    rcases mul_eq_zero.mp h4 with h | h
    · exfalso; linarith
    · exact h
  have hSb : b ≤ S := by
    by_contra hcon; push Not at hcon
    nlinarith [mul_nonneg hd0 hapos.le]
  have hs0 : 0 ≤ s := by rw [hs_def]; apply div_nonneg <;> linarith
  have e1 : 1 - muAQ α q p = s := by rw [hmu]; ring
  rw [e1]
  refine ⟨hs0, ?_, ?_⟩
  · by_contra hcon; push Not at hcon
    set s0 := c / (c + 1) with hs0_def
    have hs0pos : 0 < s0 := by positivity
    have hf0 : 0 ≤ a * s0 ^ 2 + b * s0 - d := by
      have e : (c + 1) ^ 2 * (a * s0 ^ 2 + b * s0 - d) = c * a * (p * (c + 1) - 1) := by
        rw [hs0_def, hb_def, hd_def, ← ha_eq]; field_simp; ring
      have : 0 ≤ c * a * (p * (c + 1) - 1) := by
        apply mul_nonneg (by positivity); linarith
      rw [← e] at this
      exact (mul_nonneg_iff_of_pos_left (by positivity)).mp this
    nlinarith [mul_pos (sub_pos.mpr hcon) (by positivity : 0 < a * (s + s0) + b)]
  · linarith

lemma s_lt_one (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (rLow α 1 q) 1) : α * (1 - muAQ α q p) < 1 := by
  obtain ⟨h0, h1, _⟩ := mu_root α q p hα hq hp
  have hc := GAInv_pos α q hα hq
  have : GammaAInv α q / (GammaAInv α q + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  nlinarith [hα.1, hα.2]

lemma nu_mu (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (rLow α 1 q) 1) : nu α q (muAQ α q p) = p := by
  obtain ⟨_, _, hquad⟩ := mu_root α q p hα hq hp
  have hlt := s_lt_one α q p hα hq hp
  have hc := GAInv_pos α q hα hq
  unfold nu
  set s := 1 - muAQ α q p
  have hden : 0 < GammaAInv α q * (1 - α * s) := mul_pos hc (by linarith)
  have : q ^ (α - 1) * s ^ 2 = GammaAInv α q * (1 - p) * (1 - α * s) := by linarith
  rw [this]
  have hne : 1 - α * s ≠ 0 := by linarith
  have hcne : GammaAInv α q ≠ 0 := hc.ne'
  field_simp
  ring

lemma root_unique (a b d s1 s2 : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (h1 : 0 ≤ s1) (h2 : 0 ≤ s2)
    (e1 : a * s1 ^ 2 + b * s1 - d = 0) (e2 : a * s2 ^ 2 + b * s2 - d = 0) : s1 = s2 := by
  have : (s1 - s2) * (a * (s1 + s2) + b) = 0 := by linear_combination e1 - e2
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · have : a * (s1 + s2) = 0 := by nlinarith [mul_nonneg ha.le (add_nonneg h1 h2)]
    have : s1 + s2 = 0 := by
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact h'
    linarith

lemma nu_mem (α q y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (rLow α 1 q) 1) : nu α q y ∈ Set.Icc (rLow α 1 q) 1 := by
  have hc := GAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  have ha_eq := one_add_kc α q hq.1
  rw [← hc_def] at ha_eq
  set a := q ^ (α - 1) with ha_def
  have hapos : 0 < a := by rw [← ha_eq]; nlinarith [hα.2]
  have hr : rLow α 1 q = 1 / (c + 1) := by rw [rLow_eq]
  have hy1 := hy.1; rw [hr] at hy1
  set s := 1 - y with hs
  have hs0 : 0 ≤ s := by linarith [hy.2]
  have hsle : s ≤ c / (c + 1) := by
    have : 1 / (c + 1) = 1 - c / (c + 1) := by field_simp; ring
    linarith
  have hslt1 : s < 1 := by
    have : c / (c + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hden : 0 < c * (1 - α * s) := mul_pos hc (by nlinarith [hα.1, hα.2])
  unfold nu
  rw [← hc_def, ← ha_def, ← hs]
  constructor
  · rw [hr]
    have key : a * s ^ 2 / (c * (1 - α * s)) ≤ c / (c + 1) := by
      rw [div_le_div_iff₀ hden (by linarith)]
      rw [← ha_eq]
      have hsc : s * (c + 1) ≤ c := by rw [le_div_iff₀ (by linarith)] at hsle; exact hsle
      nlinarith [mul_nonneg hs0 hs0, mul_nonneg hα.1 hs0, mul_nonneg (mul_nonneg hα.1 hs0) hc.le,
        mul_nonneg (sub_nonneg.mpr hsc) hs0, mul_nonneg (mul_nonneg (sub_nonneg.mpr hsc) hs0) hc.le,
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hsc) hs0) (sub_nonneg.mpr hα.2),
        mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hsc) hs0) (sub_nonneg.mpr hα.2)) hc.le]
    have : 1 / (c + 1) = 1 - c / (c + 1) := by field_simp; ring
    linarith
  · have : 0 ≤ a * s ^ 2 / (c * (1 - α * s)) := div_nonneg (by positivity) hden.le
    linarith

lemma mu_nu (α q y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (rLow α 1 q) 1) : muAQ α q (nu α q y) = y := by
  have hm := nu_mem α q y hα hq hy
  obtain ⟨h0, _, hquad⟩ := mu_root α q (nu α q y) hα hq hm
  have hc := GAInv_pos α q hα hq
  have ha_eq := one_add_kc α q hq.1
  have hapos : 0 < q ^ (α - 1) := by rw [← ha_eq]; nlinarith [hα.2]
  have hr : rLow α 1 q = 1 / (GammaAInv α q + 1) := rLow_eq α q
  have hlt : α * (1 - y) < 1 := by
    have h1 := hy.1; rw [hr] at h1
    have : 0 < 1 / (GammaAInv α q + 1) := by positivity
    nlinarith [hα.1, hα.2, hy.2]
  have hden : 0 < GammaAInv α q * (1 - α * (1 - y)) := mul_pos hc (by linarith)
  have hroot : q ^ (α - 1) * (1 - y) ^ 2 + α * GammaAInv α q * (1 - nu α q y) * (1 - y)
      - GammaAInv α q * (1 - nu α q y) = 0 := by
    have hne : 1 - α * (1 - y) ≠ 0 := by linarith
    have hcne : GammaAInv α q ≠ 0 := hc.ne'
    unfold nu; field_simp; ring
  have := root_unique (q ^ (α - 1)) (α * GammaAInv α q * (1 - nu α q y))
    (GammaAInv α q * (1 - nu α q y)) _ _ hapos
    (mul_nonneg (mul_nonneg hα.1 hc.le) (by linarith [hm.2])) h0 (by linarith [hy.2]) hquad hroot
  linarith

lemma nu_strict (α q y1 y2 : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (h1 : y1 ∈ Set.Icc (rLow α 1 q) 1) (h2 : y2 ∈ Set.Icc (rLow α 1 q) 1) (h12 : y1 < y2) :
    nu α q y1 < nu α q y2 := by
  have hc := GAInv_pos α q hα hq
  have ha_eq := one_add_kc α q hq.1
  have hapos : 0 < q ^ (α - 1) := by rw [← ha_eq]; nlinarith [hα.2]
  have hL := rLow_pos α q hα hq
  have hL1 := rLow_pos_lt1 α q hα hq
  set s1 := 1 - y1
  set s2 := 1 - y2
  have hs2 : 0 ≤ s2 := by linarith [h2.2]
  have hs12 : s2 < s1 := by linarith
  have hs1 : s1 < 1 := by linarith [h1.1]
  have hd1 : 0 < 1 - α * s1 := by nlinarith [hα.1, hα.2]
  have hd2 : 0 < 1 - α * s2 := by nlinarith [hα.1, hα.2]
  unfold nu
  have key : q ^ (α - 1) * s2 ^ 2 / (GammaAInv α q * (1 - α * s2)) <
      q ^ (α - 1) * s1 ^ 2 / (GammaAInv α q * (1 - α * s1)) := by
    rw [div_lt_div_iff₀ (mul_pos hc hd2) (mul_pos hc hd1)]
    have : s2 ^ 2 * (1 - α * s1) < s1 ^ 2 * (1 - α * s2) := by
      have : 0 < (s1 - s2) * (s1 + s2 - α * s1 * s2) := by
        apply mul_pos (by linarith)
        nlinarith [mul_nonneg hα.1 hs2, hα.2]
      nlinarith
    have := mul_lt_mul_of_pos_left this (mul_pos hapos hc)
    nlinarith
  linarith

lemma mu_le_iff (α q p1 p2 : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (h1 : p1 ∈ Set.Icc (rLow α 1 q) 1) (h2 : p2 ∈ Set.Icc (rLow α 1 q) 1) :
    muAQ α q p1 ≤ muAQ α q p2 ↔ p1 ≤ p2 := by
  have m1 : muAQ α q p1 ∈ Set.Icc (rLow α 1 q) 1 := by
    obtain ⟨a0, a1, _⟩ := mu_root α q p1 hα hq h1
    have hc := GAInv_pos α q hα hq
    rw [rLow_eq]; constructor
    · have : 1 / (GammaAInv α q + 1) = 1 - GammaAInv α q / (GammaAInv α q + 1) := by
        field_simp; ring
      linarith
    · linarith
  have m2 : muAQ α q p2 ∈ Set.Icc (rLow α 1 q) 1 := by
    obtain ⟨a0, a1, _⟩ := mu_root α q p2 hα hq h2
    have hc := GAInv_pos α q hα hq
    rw [rLow_eq]; constructor
    · have : 1 / (GammaAInv α q + 1) = 1 - GammaAInv α q / (GammaAInv α q + 1) := by
        field_simp; ring
      linarith
    · linarith
  constructor
  · intro h
    rcases eq_or_lt_of_le h with he | hlt
    · have := congrArg (nu α q) he
      rw [nu_mu α q p1 hα hq h1, nu_mu α q p2 hα hq h2] at this; exact this.le
    · have := nu_strict α q _ _ hα hq m1 m2 hlt
      rw [nu_mu α q p1 hα hq h1, nu_mu α q p2 hα hq h2] at this; exact this.le
  · intro h
    by_contra hcon; push Not at hcon
    have := nu_strict α q _ _ hα hq m2 m1 hcon
    rw [nu_mu α q p1 hα hq h1, nu_mu α q p2 hα hq h2] at this; linarith

lemma mu_mem (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (rLow α 1 q) 1) : muAQ α q p ∈ Set.Icc (rLow α 1 q) 1 := by
  obtain ⟨a0, a1, _⟩ := mu_root α q p hα hq hp
  have hc := GAInv_pos α q hα hq
  rw [rLow_eq]; constructor
  · have : 1 / (GammaAInv α q + 1) = 1 - GammaAInv α q / (GammaAInv α q + 1) := by
      field_simp; ring
    linarith
  · linarith

lemma nu_one (α q : ℝ) : nu α q 1 = 1 := by simp [nu]

lemma mu_lt_one (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Ico (rLow α 1 q) 1) : muAQ α q p < 1 := by
  have hpI : p ∈ Set.Icc (rLow α 1 q) 1 := ⟨hp.1, hp.2.le⟩
  rcases eq_or_lt_of_le (mu_mem α q p hα hq hpI).2 with h | h
  · have := nu_mu α q p hα hq hpI; rw [h, nu_one] at this; linarith [hp.2]
  · exact h

lemma mu_le_self (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (rLow α 1 q) 1) : muAQ α q p ≤ p := by
  have hm := mu_mem α q p hα hq hp
  have hnu := nu_mu α q p hα hq hp
  set y := muAQ α q p
  have hc := GAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  have ha_eq := one_add_kc α q hq.1
  rw [← hc_def] at ha_eq
  have hr : rLow α 1 q = 1 / (c + 1) := by rw [rLow_eq]
  have hy1 := hm.1; rw [hr] at hy1
  have hlt : α * (1 - y) < 1 := by
    have : 0 < 1 / (c + 1) := by positivity
    nlinarith [hα.1, hα.2, hm.2]
  rw [← hnu]
  unfold nu
  rw [← hc_def]
  have hden : 0 < c * (1 - α * (1 - y)) := mul_pos hc (by linarith)
  have : q ^ (α - 1) * (1 - y) ^ 2 / (c * (1 - α * (1 - y))) ≤ 1 - y := by
    rw [div_le_iff₀ hden, ← ha_eq]
    have hyc : 1 ≤ y * (c + 1) := by rw [div_le_iff₀ (by linarith)] at hy1; linarith
    have h1y : 0 ≤ 1 - y := by linarith [hm.2]
    nlinarith [mul_nonneg h1y (sub_nonneg.mpr hyc), mul_nonneg (mul_nonneg h1y (sub_nonneg.mpr hyc)) (sub_nonneg.mpr hα.2)]
  linarith

/-- `c(p − y)/(1 − y)` expressed through `y = µ(p)`. -/
noncomputable def zf (α q y : ℝ) : ℝ :=
  GammaAInv α q - q ^ (α - 1) * (1 - y) / (1 - α * (1 - y))

lemma den_pos (α q y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (rLow α 1 q) 1) : 0 < 1 - α * (1 - y) := by
  have hL := rLow_pos α q hα hq
  nlinarith [hα.1, hα.2, hy.1, hy.2]

lemma R1_formula (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Ico (rLow α 1 q) 1) :
    R1 α q p = p * GammaA α (zf α q (muAQ α q p)) / muAQ α q p := by
  have hpI : p ∈ Set.Icc (rLow α 1 q) 1 := ⟨hp.1, hp.2.le⟩
  have hm := mu_mem α q p hα hq hpI
  have hm1 := mu_lt_one α q p hα hq hp
  have hmp := mu_le_self α q p hα hq hpI
  have hnu := nu_mu α q p hα hq hpI
  unfold R1
  rw [optFun_lt α q _ hα hq ⟨hm.1, hm1⟩, Fbar_lt α q _ p hm1 hmp hp.2.le]
  congr 3
  set y := muAQ α q p
  have hd := den_pos α q y hα hq hm
  have hc := GAInv_pos α q hα hq
  conv_lhs => rw [← hnu]
  unfold nu zf
  have h1 : 1 - y ≠ 0 := by linarith
  have h2 : 1 - α * (1 - y) ≠ 0 := by linarith
  have h3 : GammaAInv α q ≠ 0 := hc.ne'
  field_simp
  ring

lemma zf_nonneg (α q y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (rLow α 1 q) 1) : 0 ≤ zf α q y := by
  have hc := GAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  have ha_eq := one_add_kc α q hq.1
  rw [← hc_def] at ha_eq
  have hd := den_pos α q y hα hq hy
  have hr : rLow α 1 q = 1 / (c + 1) := by rw [rLow_eq]
  have hy1 := hy.1; rw [hr, div_le_iff₀ (by linarith)] at hy1
  unfold zf
  rw [← hc_def, sub_nonneg, div_le_iff₀ hd, ← ha_eq]
  nlinarith [hα.1, hα.2, hy.2]

lemma zf_mono (α q y1 y2 : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (h1 : y1 ∈ Set.Icc (rLow α 1 q) 1) (h2 : y2 ∈ Set.Icc (rLow α 1 q) 1) (h12 : y1 ≤ y2) :
    zf α q y1 ≤ zf α q y2 := by
  have hd1 := den_pos α q y1 hα hq h1
  have hd2 := den_pos α q y2 hα hq h2
  have ha_eq := one_add_kc α q hq.1
  have hapos : 0 < q ^ (α - 1) := by rw [← ha_eq]; nlinarith [hα.2, GAInv_pos α q hα hq]
  unfold zf
  have : q ^ (α - 1) * (1 - y2) / (1 - α * (1 - y2)) ≤ q ^ (α - 1) * (1 - y1) / (1 - α * (1 - y1)) := by
    rw [div_le_div_iff₀ hd2 hd1]
    have : (1 - y2) * (1 - α * (1 - y1)) ≤ (1 - y1) * (1 - α * (1 - y2)) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hapos.le]
  linarith

lemma zf_rLow (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    zf α q (rLow α 1 q) = 0 := by
  have hc := GAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  have ha_eq := one_add_kc α q hq.1
  rw [← hc_def] at ha_eq
  unfold zf
  rw [rLow_eq, ← hc_def, ← ha_eq]
  have : 1 - α * (1 - 1 / (c + 1)) = (1 + (1 - α) * c) / (c + 1) := by field_simp; ring
  rw [this]
  have hpos : 0 < 1 + (1 - α) * c := by nlinarith [hα.2]
  have h1c : 1 - 1 / (c + 1) = c / (c + 1) := by field_simp; ring
  rw [h1c, mul_div_assoc', div_div_div_cancel_right₀ (by positivity : (c + 1) ≠ 0),
    mul_div_cancel_left₀ _ hpos.ne']
  ring

lemma zf_one (α q : ℝ) : zf α q 1 = GammaAInv α q := by simp [zf]

/-- semigroup property of the GPD tails. -/
lemma GA_mul (α u w : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hu : 0 ≤ u) (hw : 0 ≤ w) :
    GammaA α (u + (1 + (1 - α) * u) * w) = GammaA α u * GammaA α w := by
  by_cases h1 : α = 1
  · subst h1; simp only [GA1]; rw [← Real.exp_add]; ring_nf
  · have hk : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    unfold GammaA; rw [if_neg h1, if_neg h1, if_neg h1]
    have e : 1 + (1 - α) * (u + (1 + (1 - α) * u) * w) = (1 + (1 - α) * u) * (1 + (1 - α) * w) := by
      ring
    rw [e, Real.mul_rpow (by positivity) (by positivity)]

lemma vTilde_nonneg (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) : 0 < vTilde α := by
  unfold vTilde
  split_ifs with h0 h1
  · exact one_pos
  · exact Real.exp_pos _
  · exact Real.rpow_pos_of_pos (lt_of_le_of_ne hα.1 (Ne.symm h0)) _

lemma vTilde_le_one (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) : vTilde α ≤ 1 := by
  unfold vTilde
  split_ifs with h0 h1
  · exact le_rfl
  · rw [Real.exp_le_one_iff]; norm_num
  · have hk : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    apply Real.rpow_le_one hα.1 hα.2 (div_nonneg hα.1 hk.le)

lemma GA_inv_alpha (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα0 : α ≠ 0) :
    GammaA α (1 / α) = α * vTilde α := by
  have hαp : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hα0)
  by_cases h1 : α = 1
  · subst h1; simp [GA1, vTilde]
  · have hk : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    unfold GammaA vTilde
    rw [if_neg h1, if_neg hα0, if_neg h1]
    have e : 1 + (1 - α) * (1 / α) = α⁻¹ := by field_simp; ring
    rw [e, Real.inv_rpow hαp.le, ← Real.rpow_neg hαp.le, neg_neg]
    rw [show (1 / (1 - α)) = 1 + α / (1 - α) by field_simp; ring, Real.rpow_add hαp,
      Real.rpow_one]

lemma R3_formula (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hqL : qLow α ≤ q) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    R3 α q p = GammaAInv α q / vTilde α * (p * GammaA α (GammaAInv α q * p)) := by
  by_cases hα0 : α = 0
  · subst hα0; simp [R3, vTilde]
  have hc := GAInv_pos α q hα hq
  have hαp : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hα0)
  rw [(R3_form α q p hα hq hα0 hqL hp).2]
  have : GammaAInv α q * (1 / (α * GammaAInv α q)) = 1 / α := by field_simp
  rw [this, GA_inv_alpha α hα hα0]
  have := vTilde_nonneg α hα
  field_simp

noncomputable def G13 (α q y : ℝ) : ℝ := GammaAInv α q / vTilde α * y * GammaA α (1 - y)

noncomputable def G12 (α q y : ℝ) : ℝ := GammaA α (zf α q y) / y

lemma R1_eq_G12 (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Ico (rLow α 1 q) 1) : R1 α q p = p * G12 α q (muAQ α q p) := by
  rw [R1_formula α q p hα hq hp, G12]; ring

lemma R3_eq_G13 (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hqL : qLow α ≤ q) (hp : p ∈ Set.Ico (rLow α 1 q) 1) :
    R3 α q p = G13 α q (muAQ α q p) * R1 α q p := by
  have hpI : p ∈ Set.Icc (rLow α 1 q) 1 := ⟨hp.1, hp.2.le⟩
  have hm := mu_mem α q p hα hq hpI
  have hm1 := mu_lt_one α q p hα hq hp
  have hL := rLow_pos α q hα hq
  have hp0 : 0 ≤ p := le_trans hL.le hp.1
  rw [R3_formula α q p hα hq hqL ⟨hp0, hp.2.le⟩, R1_formula α q p hα hq hp, G13]
  set y := muAQ α q p
  have hy0 : 0 < y := lt_of_lt_of_le hL hm.1
  have hnu : nu α q y = p := nu_mu α q p hα hq hpI
  -- Γ(c p) = Γ(z) Γ(1 - y)
  have hz := zf_nonneg α q y hα hq hm
  have hsplit : GammaAInv α q * p = zf α q y + (1 + (1 - α) * zf α q y) * (1 - y) := by
    have hd := den_pos α q y hα hq hm
    have hc := GAInv_pos α q hα hq
    have ha_eq := one_add_kc α q hq.1
    rw [← hnu]
    unfold nu zf
    rw [← ha_eq]
    have h2 : 1 - α * (1 - y) ≠ 0 := by linarith
    have h2' : 1 - α + α * y ≠ 0 := by linarith
    have h3 : GammaAInv α q ≠ 0 := hc.ne'
    field_simp
    ring
  rw [hsplit, GA_mul α _ _ hα hz (by linarith)]
  field_simp

lemma GA_contOn (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) : ContinuousOn (GammaA α) (Set.Ici 0) := by
  by_cases h1 : α = 1
  · subst h1
    have : GammaA 1 = fun x => Real.exp (-x) := funext GA1
    rw [this]; exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-x)).continuousOn
  · have hk : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    have : GammaA α = fun x => (1 + (1 - α) * x) ^ (-(1 / (1 - α))) := by
      funext x; simp [GammaA, h1]
    rw [this]
    apply ContinuousOn.rpow_const (by fun_prop)
    intro x hx; left
    have : (0 : ℝ) ≤ x := hx
    nlinarith

lemma GA_le_one (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) : GammaA α x ≤ 1 := by
  have := GA_anti α 0 x hα le_rfl hx; rwa [GA_zero] at this

lemma G13_cont (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (G13 α q) (Set.Icc (rLow α 1 q) 1) := by
  have h : ContinuousOn (fun y => GammaA α (1 - y)) (Set.Icc (rLow α 1 q) 1) :=
    (GA_contOn α hα).comp (by fun_prop) (fun y hy => by
      show (0 : ℝ) ≤ 1 - y; linarith [hy.2])
  unfold G13
  exact (continuousOn_const.mul continuousOn_id).mul h

lemma zf_cont (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousOn (zf α q) (Set.Icc (rLow α 1 q) 1) := by
  unfold zf
  apply ContinuousOn.sub continuousOn_const
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro y hy; exact (den_pos α q y hα hq hy).ne'

lemma G12_cont (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousOn (G12 α q) (Set.Icc (rLow α 1 q) 1) := by
  have h : ContinuousOn (fun y => GammaA α (zf α q y)) (Set.Icc (rLow α 1 q) 1) :=
    (GA_contOn α hα).comp (zf_cont α q hα hq) (fun y hy => zf_nonneg α q y hα hq hy)
  unfold G12
  apply h.div continuousOn_id
  intro y hy; exact (lt_of_lt_of_le (rLow_pos α q hα hq) hy.1).ne'

lemma G13_mono (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    MonotoneOn (G13 α q) (Set.Icc (rLow α 1 q) 1) := by
  intro y1 h1 y2 h2 h12
  have hL := rLow_pos α q hα hq
  have hC : 0 ≤ GammaAInv α q / vTilde α :=
    div_nonneg (GAInv_pos α q hα hq).le (vTilde_nonneg α hα).le
  unfold G13
  rw [mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC
  apply mul_le_mul h12 (GA_anti α _ _ hα (by linarith [h2.2]) (by linarith))
    (GA_pos α _ hα (by linarith [h1.2])).le (by linarith [h2.1])

lemma G12_anti (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    AntitoneOn (G12 α q) (Set.Icc (rLow α 1 q) 1) := by
  intro y1 h1 y2 h2 h12
  have hL := rLow_pos α q hα hq
  unfold G12
  apply div_le_div₀ (GA_pos α _ hα (zf_nonneg α q y1 hα hq h1)).le
    (GA_anti α _ _ hα (zf_nonneg α q y1 hα hq h1) (zf_mono α q y1 y2 hα hq h1 h2 h12))
    (lt_of_lt_of_le hL h1.1) h12

lemma G12_rLow (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    G12 α q (rLow α 1 q) = 1 / rLow α 1 q := by
  unfold G12; rw [zf_rLow α q hα hq, GA_zero]

lemma G12_one (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    G12 α q 1 = q := by
  unfold G12; rw [zf_one, GA_GAInv α q hα hq.1, div_one]

lemma G13_one (α q : ℝ) : G13 α q 1 = GammaAInv α q / vTilde α := by
  simp [G13, GA_zero]

lemma rev_vtilde (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x * GammaA α x ≤ vTilde α := by
  by_cases hα0 : α = 0
  · subst hα0
    rw [GA0]; simp only [vTilde, if_true]
    rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
  · have hαp : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hα0)
    have h := xG_mono α 1 x (1 / α) hα one_pos hx0
      (by rw [le_div_iff₀ hαp]; nlinarith [hα.2]) (by field_simp; rfl)
    rw [one_mul, one_mul, GA_inv_alpha α hα hα0] at h
    have : 1 / α * (α * vTilde α) = vTilde α := by field_simp
    linarith

lemma G13_rLow (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    G13 α q (rLow α 1 q) ≤ 1 := by
  have hc := GAInv_pos α q hα hq
  have hv := vTilde_nonneg α hα
  unfold G13
  rw [rLow_eq]
  set c := GammaAInv α q
  have e1 : 1 - 1 / (c + 1) = c / (c + 1) := by field_simp; ring
  rw [e1]
  have h := rev_vtilde α (c / (c + 1)) hα (by positivity)
    (by rw [div_le_one (by linarith)]; linarith)
  have e2 : c / vTilde α * (1 / (c + 1)) * GammaA α (c / (c + 1)) =
      (c / (c + 1) * GammaA α (c / (c + 1))) / vTilde α := by field_simp
  rw [e2, div_le_one hv]; exact h

lemma qLow_le_GV (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) : qLow α ≤ GammaA α (vTilde α) := by
  by_cases hα0 : α = 0
  · subst hα0; simp only [qLow, if_true]; exact (GA_pos 0 _ hα (vTilde_nonneg 0 hα).le).le
  · have hαp : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hα0)
    simp only [qLow, hα0, if_false]
    apply GA_anti α _ _ hα (vTilde_nonneg α hα).le
    have := vTilde_le_one α hα
    have : 1 ≤ 1 / α := by rw [le_div_iff₀ hαp]; linarith [hα.2]
    linarith

lemma mu_one (α q : ℝ) : muAQ α q 1 = 1 := by simp [muAQ, Delta]

lemma Fbar_one_r (α q v : ℝ) (hv0 : 0 ≤ v) :
    Fbar α 1 q 1 v = if v ≤ 1 then GammaA α (GammaAInv α q * v) else 0 := by
  simp [Fbar, Gbar, not_lt.mpr hv0]

lemma R1_one_le (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    R1 α q 1 ≤ 1 := by
  have hc := GAInv_pos α q hα hq
  unfold R1
  rw [mu_one, Fbar_one_r α q 1 zero_le_one, if_pos le_rfl, mul_one,
    GA_GAInv α q hα hq.1, one_mul]
  have hq1 : q ≤ optFun (Fbar α 1 q 1) := by
    unfold optFun
    have hmem : (1 : ℝ) * Fbar α 1 q 1 1 ∈ (fun v : ℝ => v * Fbar α 1 q 1 v) '' Set.Ici 0 :=
      ⟨1, by norm_num, rfl⟩
    have hb : BddAbove ((fun v : ℝ => v * Fbar α 1 q 1 v) '' Set.Ici 0) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨v, hv, rfl⟩
      have hv0 : (0 : ℝ) ≤ v := hv
      simp only
      rw [Fbar_one_r α q v hv0]
      split_ifs with h
      · have := GA_le_one α (GammaAInv α q * v) hα (by positivity)
        nlinarith [(GA_pos α (GammaAInv α q * v) hα (by positivity)).le]
      · simp
    have := le_csSup hb hmem
    rw [Fbar_one_r α q 1 zero_le_one, if_pos le_rfl, mul_one, GA_GAInv α q hα hq.1, one_mul]
      at this
    exact this
  rw [div_le_one (by linarith [hq.1])]; exact hq1

lemma R1_one (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hac : α * GammaAInv α q ≤ 1) : R1 α q 1 = 1 := by
  unfold R1
  rw [mu_one, optFun_rw α 1 q 1 hα one_pos hq (Or.inr ⟨le_rfl, by linarith⟩)]
  have : 0 < Fbar α 1 q 1 1 := by
    rw [Fbar_one_r α q 1 zero_le_one, if_pos le_rfl]; exact GA_pos α _ hα (by nlinarith [GAInv_pos α q hα hq])
  field_simp

lemma R1_nonneg (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Ico (rLow α 1 q) 1) : 0 ≤ R1 α q p := by
  have hpI : p ∈ Set.Icc (rLow α 1 q) 1 := ⟨hp.1, hp.2.le⟩
  have hm := mu_mem α q p hα hq hpI
  have hL := rLow_pos α q hα hq
  rw [R1_formula α q p hα hq hp]
  apply div_nonneg (mul_nonneg (by linarith [hp.1]) (GA_pos α _ hα (zf_nonneg α q _ hα hq hm)).le)
  linarith [hm.1]

lemma rev_dec (α c r x v : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hc : 0 < c) (hr0 : 0 < r)
    (hr1 : r < 1) (hrL : 1 ≤ c * r / (1 - r)) (hx : r ≤ x) (hv : x ≤ v) :
    v * GammaA α (c * (v - r) / (1 - r)) ≤ x * GammaA α (c * (x - r) / (1 - r)) := by
  set β := c / (1 - r) with hβ
  have h1r : 0 < 1 - r := by linarith
  have hβ0 : 0 < β := div_pos hc h1r
  have hβr : 1 ≤ β * r := by rw [hβ, div_mul_eq_mul_div]; exact hrL
  set u := β * (x - r) with hu
  have hu0 : 0 ≤ u := mul_nonneg hβ0.le (by linarith)
  have hku : 0 < 1 + (1 - α) * u := by nlinarith [hα.2]
  set β' := β / (1 + (1 - α) * u) with hβ'
  set w := β' * (v - x) with hw
  have hw0 : 0 ≤ w := mul_nonneg (div_nonneg hβ0.le hku.le) (by linarith)
  have hkune : 1 + (1 - α) * u ≠ 0 := hku.ne'
  have hsplit : c * (v - r) / (1 - r) = u + (1 + (1 - α) * u) * w := by
    rw [hw, hβ', show (1 + (1 - α) * u) * (β / (1 + (1 - α) * u) * (v - x)) = β * (v - x) by
      field_simp]
    rw [hu, hβ]; field_simp; ring
  have hsplitx : c * (x - r) / (1 - r) = u := by rw [hu, hβ]; field_simp
  rw [hsplit, hsplitx, GA_mul α u w hα hu0 hw0]
  have hβ'x : 1 ≤ β' * x := by
    rw [hβ', div_mul_eq_mul_div, le_div_iff₀ hku, one_mul, hu]
    nlinarith [hα.1, hα.2]
  have hA := lemA α β' x v hα (by linarith) hβ'x hv
  have hGu := GA_pos α u hα hu0
  rw [← hw] at hA
  nlinarith

lemma R1_formula0 (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Ico (rLow α 1 q) 1) :
    R1 α q p = p * GammaA α (GammaAInv α q * (p - muAQ α q p) / (1 - muAQ α q p)) / muAQ α q p := by
  have hpI : p ∈ Set.Icc (rLow α 1 q) 1 := ⟨hp.1, hp.2.le⟩
  have hm := mu_mem α q p hα hq hpI
  have hm1 := mu_lt_one α q p hα hq hp
  have hmp := mu_le_self α q p hα hq hpI
  unfold R1
  rw [optFun_lt α q _ hα hq ⟨hm.1, hm1⟩, Fbar_lt α q _ p hm1 hmp hp.2.le]

lemma R1_anti (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    AntitoneOn (R1 α q) (Set.Ico (rLow α 1 q) 1) := by
  intro p1 h1 p2 h2 h12
  have hp1I : p1 ∈ Set.Icc (rLow α 1 q) 1 := ⟨h1.1, h1.2.le⟩
  have hm := mu_mem α q p1 hα hq hp1I
  have hm1 := mu_lt_one α q p1 hα hq h1
  have hmp := mu_le_self α q p1 hα hq hp1I
  set y := muAQ α q p1 with hy
  have hL := rLow_pos α q hα hq
  have hy0 : 0 < y := lt_of_lt_of_le hL hm.1
  have hc := GAInv_pos α q hα hq
  rcases eq_or_lt_of_le h12 with he | hlt
  · rw [he]
  have hyp2 : y < p2 := lt_of_le_of_lt hmp hlt
  have hb := ((propD1_worst_terms α hα q hq).1 p2 ⟨lt_of_le_of_lt hm.1 hyp2, h2.2⟩).2
    ⟨y, ⟨hm.1, hyp2⟩, rfl⟩
  simp only at hb
  rw [Fbar_lt α q y p2 hm1 hyp2.le h2.2.le] at hb
  rw [R1_formula0 α q p1 hα hq h1, ← hy]
  refine le_trans hb ?_
  apply div_le_div_of_nonneg_right _ hy0.le
  have hrL : 1 ≤ GammaAInv α q * y / (1 - y) := by
    have := hm.1; rw [rLow_eq, div_le_iff₀ (by linarith)] at this
    rw [le_div_iff₀ (by linarith)]; linarith
  exact rev_dec α _ y p1 p2 hα hc hy0 hm1 hrL hmp h12

lemma c_gt_vt (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (h : q < GammaA α (vTilde α)) : vTilde α < GammaAInv α q := by
  have := GAInv_anti α _ _ hα hq.1 h
  rwa [GAInv_GA α _ hα (vTilde_nonneg α hα).le] at this

lemma c_le_vt (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (h : GammaA α (vTilde α) ≤ q) : GammaAInv α q ≤ vTilde α := by
  rcases eq_or_lt_of_le h with he | hlt
  · rw [← he, GAInv_GA α _ hα (vTilde_nonneg α hα).le]
  · have := GAInv_anti α _ _ hα (GA_pos α _ hα (vTilde_nonneg α hα).le) hlt
    rw [GAInv_GA α _ hα (vTilde_nonneg α hα).le] at this; exact this.le

lemma ac_le_one (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hqL : qLow α ≤ q) : α * GammaAInv α q ≤ 1 := by
  by_cases hα0 : α = 0
  · subst hα0; simp
  · have hc := GAInv_pos α q hα hq
    have h := (R3_form α q 0 hα hq hα0 hqL ⟨le_rfl, zero_le_one⟩).1
    rw [le_div_iff₀ (by have := lt_of_le_of_ne hα.1 (Ne.symm hα0); positivity)] at h
    linarith

lemma xexp_strictMono : StrictMonoOn (fun w : ℝ => w * Real.exp w) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only
  have := Real.exp_lt_exp.mpr hab
  have ha0 : (0 : ℝ) ≤ a := ha
  nlinarith [Real.exp_pos a]

lemma W_spec (x : ℝ) (hx : 0 ≤ x) : 0 ≤ lambertW x ∧ lambertW x * Real.exp (lambertW x) = x := by
  have hex : ∃ w : ℝ, 0 ≤ w ∧ w * Real.exp w = x := by
    have hc : ContinuousOn (fun w : ℝ => w * Real.exp w) (Set.Icc 0 x) := by fun_prop
    have hmem : x ∈ Set.Icc ((fun w : ℝ => w * Real.exp w) 0) ((fun w : ℝ => w * Real.exp w) x) := by
      simp only [zero_mul]
      refine ⟨hx, ?_⟩
      have := Real.add_one_le_exp x
      nlinarith
    obtain ⟨w, hw, hwx⟩ := intermediate_value_Icc hx hc hmem
    exact ⟨w, hw.1, hwx⟩
  unfold lambertW
  rw [dif_pos hex]
  exact Classical.choose_spec hex

lemma W_unique (x y : ℝ) (hy : 0 ≤ y) (h : y * Real.exp y = x) : lambertW x = y := by
  have hx : 0 ≤ x := by rw [← h]; positivity
  obtain ⟨h0, h1⟩ := W_spec x hx
  exact xexp_strictMono.injOn h0 hy (h1.trans h.symm)

lemma W_e : lambertW (Real.exp 1) = 1 := W_unique _ 1 zero_le_one (by simp)

lemma exp_neg_exp_gt : (0.53 : ℝ) < Real.exp (-Real.exp (-1)) := by
  have h1 : Real.exp (-1) < 0.37 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith [show (1 : ℝ) / 0.37 < 2.7182818283 by norm_num, show (0.37 : ℝ)⁻¹ = 1 / 0.37 by norm_num]
  have h2 := Real.add_one_le_exp (-Real.exp (-1))
  linarith

lemma c1 (q : ℝ) : GammaAInv 1 q = Real.log q⁻¹ := by
  unfold GammaAInv; simp [Real.log_inv]

lemma rLow1 (q : ℝ) : rLow 1 1 q = 1 / (Real.log q⁻¹ + 1) := by rw [rLow_eqw, c1]

lemma qLow1 : qLow 1 = Real.exp (-1) := by simp [qLow, GA1]

lemma GV1 : GammaA 1 (vTilde 1) = Real.exp (-Real.exp (-1)) := by simp [vTilde, GA1]

lemma L_pos (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) : 0 < Real.log q⁻¹ := by
  rw [Real.log_inv]; have := Real.log_neg hq.1 hq.2; linarith

lemma L_le_one (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hqL : Real.exp (-1) ≤ q) :
    Real.log q⁻¹ ≤ 1 := by
  rw [Real.log_inv]
  have := Real.log_le_log (Real.exp_pos _) hqL
  rw [Real.log_exp] at this; linarith

lemma exp_L (q : ℝ) (hq : 0 < q) : Real.exp (-Real.log q⁻¹) = q := by
  rw [Real.log_inv, neg_neg, Real.exp_log hq]


lemma cross13 (α q y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hqL : qLow α ≤ q) (hyI : y ∈ Set.Icc (rLow α 1 q) 1) (hy1 : y < 1) (hGy : G13 α q y = 1) :
    nu α q y ∈ Set.Icc (rLow α 1 q) 1 ∧
      (∀ p ∈ Set.Icc (rLow α 1 q) (nu α q y), R3 α q p ≤ R1 α q p) ∧
      (∀ p ∈ Set.Ico (nu α q y) 1, R1 α q p ≤ R3 α q p) := by
  have hL1 := rLow_pos_lt1 α q hα hq
  have h1I : (1 : ℝ) ∈ Set.Icc (rLow α 1 q) 1 := ⟨hL1.le, le_rfl⟩
  refine ⟨nu_mem α q y hα hq hyI, ?_, ?_⟩
  · intro p hp
    have hp13 : nu α q y < 1 := by
      have := nu_strict α q y 1 hα hq hyI h1I hy1; rwa [nu_one] at this
    have hpI : p ∈ Set.Icc (rLow α 1 q) 1 := ⟨hp.1, by linarith [hp.2]⟩
    have hpo : p ∈ Set.Ico (rLow α 1 q) 1 := ⟨hp.1, by linarith [hp.2]⟩
    have hmu : muAQ α q p ≤ y := by
      have := (mu_le_iff α q p (nu α q y) hα hq hpI (nu_mem α q y hα hq hyI)).mpr hp.2
      rwa [mu_nu α q y hα hq hyI] at this
    have hG : G13 α q (muAQ α q p) ≤ 1 := by
      rw [← hGy]; exact G13_mono α q hα hq (mu_mem α q p hα hq hpI) hyI hmu
    rw [R3_eq_G13 α q p hα hq hqL hpo]
    have := R1_nonneg α q p hα hq hpo
    nlinarith
  · intro p hp
    have hpI : p ∈ Set.Icc (rLow α 1 q) 1 := ⟨le_trans (nu_mem α q y hα hq hyI).1 hp.1, hp.2.le⟩
    have hpo : p ∈ Set.Ico (rLow α 1 q) 1 := ⟨hpI.1, hp.2⟩
    have hmu : y ≤ muAQ α q p := by
      have := (mu_le_iff α q (nu α q y) p hα hq (nu_mem α q y hα hq hyI) hpI).mpr hp.1
      rwa [mu_nu α q y hα hq hyI] at this
    have hG : 1 ≤ G13 α q (muAQ α q p) := by
      rw [← hGy]; exact G13_mono α q hα hq hyI (mu_mem α q p hα hq hpI) hmu
    rw [R3_eq_G13 α q p hα hq hqL hpo]
    have := R1_nonneg α q p hα hq hpo
    nlinarith

lemma cross12 (α q y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hyI : y ∈ Set.Icc (rLow α 1 q) 1) (hy1 : y < 1) (hGy : G12 α q y = 1) :
    (∀ p ∈ Set.Icc (rLow α 1 q) (nu α q y), R2 p ≤ R1 α q p) ∧
      (∀ p ∈ Set.Icc (nu α q y) 1, R1 α q p ≤ R2 p) := by
  have hL1 := rLow_pos_lt1 α q hα hq
  have h1I : (1 : ℝ) ∈ Set.Icc (rLow α 1 q) 1 := ⟨hL1.le, le_rfl⟩
  have hp12 : nu α q y < 1 := by
    have := nu_strict α q y 1 hα hq hyI h1I hy1; rwa [nu_one] at this
  refine ⟨?_, ?_⟩
  · intro p hp
    have hpI : p ∈ Set.Icc (rLow α 1 q) 1 := ⟨hp.1, by linarith [hp.2]⟩
    have hpo : p ∈ Set.Ico (rLow α 1 q) 1 := ⟨hp.1, by linarith [hp.2]⟩
    have hmu : muAQ α q p ≤ y := by
      have := (mu_le_iff α q p (nu α q y) hα hq hpI (nu_mem α q y hα hq hyI)).mpr hp.2
      rwa [mu_nu α q y hα hq hyI] at this
    have hG : 1 ≤ G12 α q (muAQ α q p) := by
      rw [← hGy]; exact G12_anti α q hα hq (mu_mem α q p hα hq hpI) hyI hmu
    rw [R1_eq_G12 α q p hα hq hpo, R2_eq p hpI.2]
    have : 0 ≤ p := by linarith [hp.1, rLow_pos α q hα hq]
    nlinarith
  · intro p hp
    rcases eq_or_lt_of_le hp.2 with h1 | h1
    · rw [h1, R2_eq 1 le_rfl]; exact R1_one_le α q hα hq
    have hpI : p ∈ Set.Icc (rLow α 1 q) 1 := ⟨le_trans (nu_mem α q y hα hq hyI).1 hp.1, hp.2⟩
    have hpo : p ∈ Set.Ico (rLow α 1 q) 1 := ⟨hpI.1, h1⟩
    have hmu : y ≤ muAQ α q p := by
      have := (mu_le_iff α q (nu α q y) p hα hq (nu_mem α q y hα hq hyI) hpI).mpr hp.1
      rwa [mu_nu α q y hα hq hyI] at this
    have hG : G12 α q (muAQ α q p) ≤ 1 := by
      rw [← hGy]; exact G12_anti α q hα hq hyI (mu_mem α q p hα hq hpI) hmu
    rw [R1_eq_G12 α q p hα hq hpo, R2_eq p hpI.2]
    have : 0 ≤ p := by linarith [hpI.1, rLow_pos α q hα hq]
    nlinarith

/-! ## `α = 0` -/

lemma qpow0 (q : ℝ) : q ^ ((0 : ℝ) - 1) = q⁻¹ := by norm_num; exact Real.rpow_neg_one q

lemma nu0 (q y : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    nu 0 q y = 1 - (1 - y) ^ 2 / (1 - q) := by
  unfold nu; rw [qpow0, c0]
  have : (1 : ℝ) - q ≠ 0 := by linarith [hq.2]
  have : q ≠ 0 := hq.1.ne'
  field_simp; ring

theorem part0 :
    ((1 / 4 : ℝ) ∈ Set.Icc (qLow 0) (GammaA 0 (vTilde 0)) ∩ Set.Ioo 0 1 ∧
      (∀ q ∈ Set.Icc (qLow 0) (GammaA 0 (vTilde 0)) ∩ Set.Ioo 0 1,
        (1 - (1 - 2 * q) ^ 2 / (1 - q) = 1 - (1 - Real.sqrt q) ^ 2 / (1 - q) ↔ q = 1 / 4) ∧
        (1 - (1 - 2 * q) ^ 2 / (1 - q) ≤ 1 - (1 - Real.sqrt q) ^ 2 / (1 - q) ↔ q ≤ 1 / 4)) ∧
      (∀ q ∈ Set.Ico (qLow 0) (GammaA 0 (vTilde 0)) ∩ Set.Ioo 0 1,
        1 - (1 - 2 * q) ^ 2 / (1 - q) ∈ Set.Icc (rLow 0 1 q) 1 ∧
        (∀ p ∈ Set.Icc (rLow 0 1 q) (1 - (1 - 2 * q) ^ 2 / (1 - q)), R3 0 q p ≤ R1 0 q p) ∧
        (∀ p ∈ Set.Ico (1 - (1 - 2 * q) ^ 2 / (1 - q)) 1, R1 0 q p ≤ R3 0 q p)) ∧
      (∀ q ∈ Set.Ioo (0 : ℝ) 1,
        (∀ p ∈ Set.Icc (rLow 0 1 q) (1 - (1 - Real.sqrt q) ^ 2 / (1 - q)), R2 p ≤ R1 0 q p) ∧
        (∀ p ∈ Set.Icc (1 - (1 - Real.sqrt q) ^ 2 / (1 - q)) 1, R1 0 q p ≤ R2 p))) := by
  have hα : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rw [GV0, qLow0]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩, ?_, ?_, ?_⟩
  · rintro q ⟨⟨_, hq2⟩, hq0, hq1⟩
    have h1q : 0 < 1 - q := by linarith
    set t := Real.sqrt q with ht
    have ht0 : 0 < t := Real.sqrt_pos.mpr hq0
    have ht2 : t ^ 2 = q := Real.sq_sqrt hq0.le
    have ht1 : t < 1 := by nlinarith
    have key : ∀ A B : ℝ, (1 - A / (1 - q) ≤ 1 - B / (1 - q) ↔ B ≤ A) := by
      intro A B; rw [sub_le_sub_iff_left, div_le_div_iff_of_pos_right h1q]
    have key2 : ∀ A B : ℝ, (1 - A / (1 - q) = 1 - B / (1 - q) ↔ B = A) := by
      intro A B; constructor
      · intro h; have := h; field_simp at this; linarith
      · intro h; rw [h]
    rw [key, key2]
    have hfac : (1 - 2 * q) ^ 2 - (1 - t) ^ 2 = t * (1 - 2 * t) * (2 - t - 2 * t ^ 2) := by
      rw [← ht2]; ring
    have hpos : 0 < t * (2 - t - 2 * t ^ 2) := by
      apply mul_pos ht0; nlinarith
    have hq4 : q ≤ 1 / 4 ↔ t ≤ 1 / 2 := by
      rw [← ht2]; constructor
      · intro h; nlinarith
      · intro h; nlinarith
    have hq4' : q = 1 / 4 ↔ t = 1 / 2 := by
      rw [← ht2]; constructor
      · intro h; nlinarith
      · intro h; rw [h]; norm_num
    rw [hq4, hq4']
    constructor
    · constructor
      · intro h
        have : t * (1 - 2 * t) * (2 - t - 2 * t ^ 2) = 0 := by rw [← hfac, h]; ring
        have : (1 - 2 * t) * (t * (2 - t - 2 * t ^ 2)) = 0 := by linarith
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · linarith
      · intro h; rw [← ht2] at *; rw [h]; norm_num
    · constructor
      · intro h
        have : 0 ≤ (1 - 2 * t) * (t * (2 - t - 2 * t ^ 2)) := by nlinarith
        by_contra hcon; push Not at hcon
        nlinarith
      · intro h
        have : 0 ≤ (1 - 2 * t) * (t * (2 - t - 2 * t ^ 2)) :=
          mul_nonneg (by linarith) hpos.le
        nlinarith
  · rintro q ⟨⟨_, hq2⟩, hq0, hq1⟩
    have hq : q ∈ Set.Ioo (0 : ℝ) 1 := ⟨hq0, hq1⟩
    have hyI : 2 * q ∈ Set.Icc (rLow 0 1 q) 1 := by rw [rLow0 q hq0]; constructor <;> linarith
    have hG : G13 0 q (2 * q) = 1 := by
      unfold G13; rw [c0, GA0]; simp only [vTilde, if_true, div_one]
      rw [show (1 : ℝ) + (1 - 2 * q) = 2 * (1 - q) by ring]
      have : (1 : ℝ) - q ≠ 0 := by linarith
      have : q ≠ 0 := hq0.ne'
      field_simp
    have h := cross13 0 q (2 * q) hα hq (by rw [qLow0]; exact hq0.le) hyI (by linarith) hG
    rw [nu0 q (2 * q) hq] at h
    exact h
  · intro q hq
    have hq0 := hq.1
    have ht0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
    have ht2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
    have ht1 : Real.sqrt q < 1 := by nlinarith [hq.2]
    have hyI : Real.sqrt q ∈ Set.Icc (rLow 0 1 q) 1 := by
      rw [rLow0 q hq0]; constructor <;> nlinarith
    have hG : G12 0 q (Real.sqrt q) = 1 := by
      unfold G12 zf; rw [c0, GA0, qpow0]
      have hq' : q ≠ 0 := hq0.ne'
      have e : 1 + (1 / q - 1 - q⁻¹ * (1 - Real.sqrt q) / (1 - 0 * (1 - Real.sqrt q)))
          = Real.sqrt q / q := by field_simp; ring
      rw [e, inv_div, div_div, ← sq, ht2, div_self hq']
    have h := cross12 0 q (Real.sqrt q) hα hq hyI ht1 hG
    rw [nu0 q _ hq] at h
    exact h
lemma hE1 : Real.exp (1000 / 1341) ≤ 2.108 := by
  have h := Real.exp_bound' (x := 1000 / 1341) (by norm_num) (by norm_num) (n := 9) (by norm_num)
  refine le_trans h ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma hE2 : (2.097 : ℝ) ≤ Real.exp (20 / 27) := by
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg (x := 20 / 27) (by norm_num) 9)
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma hT1 : (1.341 : ℝ) < Real.exp 0.295 := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (x := 0.295) (by norm_num) 9)
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma hT2 : Real.exp 0.2938 < 1.35 := by
  have h := Real.exp_bound' (x := 0.2938) (by norm_num) (by norm_num) (n := 9) (by norm_num)
  refine lt_of_le_of_lt h ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma hM1 : (1 / 0.53 : ℝ) ≤ Real.exp 0.6361 := by
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg (x := 0.6361) (by norm_num) 9)
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma hM2 : Real.exp 0.6438 ≤ 1 / 0.52 := by
  have h := Real.exp_bound' (x := 0.6438) (by norm_num) (by norm_num) (n := 9) (by norm_num)
  refine le_trans h ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]


/-! ## `α = 1` -/

lemma W_zero : lambertW 0 = 0 := W_unique 0 0 le_rfl (by simp)

noncomputable def psi (u : ℝ) : ℝ := Real.log u + u - 1 - u * Real.exp (-u⁻¹)

noncomputable def Lf (u : ℝ) : ℝ := u * Real.exp (-u⁻¹)

lemma Lf_strictMono : StrictMonoOn Lf (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  unfold Lf
  have h1 : Real.exp (-x⁻¹) < Real.exp (-y⁻¹) := by
    rw [Real.exp_lt_exp, neg_lt_neg_iff]; exact inv_strictAnti₀ hx0 hxy
  have := Real.exp_pos (-x⁻¹)
  nlinarith

lemma psi_hasDeriv (x : ℝ) (hx : 0 < x) :
    HasDerivAt psi (x⁻¹ + 1 - (1 * Real.exp (-x⁻¹) + x * (Real.exp (-x⁻¹) * -(-(x ^ 2)⁻¹)))) x := by
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h2 : HasDerivAt (fun u : ℝ => -u⁻¹) (-(-(x ^ 2)⁻¹)) x := (hasDerivAt_inv hx.ne').neg
  have h3 := h2.exp
  have h4 := (hasDerivAt_id' x).mul h3
  have h5 := ((h1.add (hasDerivAt_id' x)).sub_const 1).sub h4
  unfold psi
  exact h5

lemma psi_strictMono : StrictMonoOn psi (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · have : ContinuousOn (fun u : ℝ => Real.log u + u - 1 - u * Real.exp (-u⁻¹)) (Set.Ioi 0) := by
      apply ContinuousOn.sub
      · exact ((Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)).add continuousOn_id).sub
          continuousOn_const
      · apply continuousOn_id.mul
        apply Real.continuous_exp.comp_continuousOn
        exact (continuousOn_inv₀.mono (fun x hx => ne_of_gt hx)).neg
    exact this
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : (0 : ℝ) < x := hx
    rw [(psi_hasDeriv x hx0).deriv]
    have he : Real.exp (-x⁻¹) < 1 := by
      have : Real.exp (-x⁻¹) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (by have := inv_pos.mpr hx0; linarith)
      rwa [Real.exp_zero] at this
    have e : x⁻¹ + 1 - (1 * Real.exp (-x⁻¹) + x * (Real.exp (-x⁻¹) * -(-(x ^ 2)⁻¹)))
        = (1 + x⁻¹) * (1 - Real.exp (-x⁻¹)) := by
      field_simp; ring
    rw [e]
    have : 0 < x⁻¹ := inv_pos.mpr hx0
    exact mul_pos (by linarith) (by linarith)

lemma psi_lo : psi 1.341 < 0 := by
  unfold psi
  have hl : Real.log 1.341 < 0.295 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr hT1
  have hinv : (1.341 : ℝ)⁻¹ = 1000 / 1341 := by norm_num
  rw [hinv, Real.exp_neg]
  have hE := hE1
  have hpos := Real.exp_pos (1000 / 1341 : ℝ)
  have : (1.341 : ℝ) / 2.108 ≤ 1.341 * (Real.exp (1000 / 1341))⁻¹ := by
    rw [← div_eq_mul_inv]; exact div_le_div_of_nonneg_left (by norm_num) hpos hE
  norm_num at this ⊢
  linarith

lemma psi_hi : 0 < psi 1.35 := by
  unfold psi
  have hl : 0.2938 < Real.log 1.35 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr hT2
  have hinv : (1.35 : ℝ)⁻¹ = 20 / 27 := by norm_num
  rw [hinv, Real.exp_neg]
  have hE := hE2
  have : 1.35 * (Real.exp (20 / 27))⁻¹ ≤ (1.35 : ℝ) / 2.097 := by
    rw [← div_eq_mul_inv]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hE
  norm_num at this ⊢
  linarith

lemma psi_cont : ContinuousOn psi (Set.Icc 1.341 1.35) := by
  apply ContinuousOn.sub
  · exact ((Real.continuousOn_log.mono (fun x hx => by
      have : (1.341 : ℝ) ≤ x := hx.1; exact (show (0:ℝ) < x by linarith).ne')).add
        continuousOn_id).sub continuousOn_const
  · apply continuousOn_id.mul
    apply Real.continuous_exp.comp_continuousOn
    exact (continuousOn_inv₀.mono (fun x hx => by
      have : (1.341 : ℝ) ≤ x := hx.1; exact (show (0:ℝ) < x by linarith).ne')).neg

lemma psi_root : ∃ u ∈ Set.Ioo (1.341 : ℝ) 1.35, psi u = 0 := by
  obtain ⟨u, hu, hpu⟩ := intermediate_value_Icc (by norm_num) psi_cont
    ⟨psi_lo.le, psi_hi.le⟩
  refine ⟨u, ⟨?_, ?_⟩, hpu⟩
  · rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h] at hpu; linarith [psi_lo]
    · exact h
  · rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h] at hpu; linarith [psi_hi]
    · exact h

lemma Lf_lo : (0.6361 : ℝ) ≤ Lf 1.341 := by
  unfold Lf
  have hinv : (1.341 : ℝ)⁻¹ = 1000 / 1341 := by norm_num
  rw [hinv, Real.exp_neg]
  have hpos := Real.exp_pos (1000 / 1341 : ℝ)
  have : (1.341 : ℝ) / 2.108 ≤ 1.341 * (Real.exp (1000 / 1341))⁻¹ := by
    rw [← div_eq_mul_inv]; exact div_le_div_of_nonneg_left (by norm_num) hpos hE1
  norm_num at this ⊢; linarith

lemma Lf_hi : Lf 1.35 ≤ (0.6438 : ℝ) := by
  unfold Lf
  have hinv : (1.35 : ℝ)⁻¹ = 20 / 27 := by norm_num
  rw [hinv, Real.exp_neg]
  have : 1.35 * (Real.exp (20 / 27))⁻¹ ≤ (1.35 : ℝ) / 2.097 := by
    rw [← div_eq_mul_inv]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hE2
  norm_num at this ⊢; linarith

/-- the quantities attached to `q`. -/
lemma q_facts (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    0 < lambertW (1 / Real.log q⁻¹) ∧
    Real.log q⁻¹ = Lf (lambertW (1 / Real.log q⁻¹))⁻¹ ∧
    0 ≤ lambertW (Real.exp 1 / q) ∧
    lambertW (Real.exp 1 / q) * Real.exp (lambertW (Real.exp 1 / q)) = Real.exp (1 + Real.log q⁻¹) := by
  have hL := L_pos q hq
  set L := Real.log q⁻¹ with hLdef
  obtain ⟨ha0, hae⟩ := W_spec (1 / L) (by positivity)
  obtain ⟨hb0, hbe⟩ := W_spec (Real.exp 1 / q) (by have := hq.1; positivity)
  set a := lambertW (1 / L)
  have ha : 0 < a := by
    rcases eq_or_lt_of_le ha0 with h | h
    · rw [← h] at hae; simp at hae; exact absurd hae.symm (by positivity)
    · exact h
  refine ⟨ha, ?_, hb0, ?_⟩
  · unfold Lf
    rw [inv_inv]
    have : L = 1 / (a * Real.exp a) := by rw [hae]; field_simp
    rw [this, Real.exp_neg]; field_simp
  · rw [hbe, Real.exp_add, hLdef, Real.exp_log (inv_pos.mpr hq.1)]; ring

lemma hfun_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) : x + 1 / x ≤ y + 1 / y ↔ x ≤ y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have e : y + 1 / y - (x + 1 / x) = (y - x) * (x * y - 1) / (x * y) := by field_simp; ring
  constructor
  · intro h
    by_contra hcon; push Not at hcon
    have h1 : (y - x) * (x * y - 1) / (x * y) < 0 := by
      apply div_neg_of_neg_of_pos _ (by positivity)
      apply mul_neg_of_neg_of_pos (by linarith); nlinarith
    linarith
  · intro h
    have : 0 ≤ (y - x) * (x * y - 1) / (x * y) :=
      div_nonneg (mul_nonneg (by linarith) (by nlinarith)) (by positivity)
    linarith

lemma hfun_eq (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) : x + 1 / x = y + 1 / y ↔ x = y := by
  constructor
  · intro h
    exact le_antisymm ((hfun_le x y hx hy).mp h.le) ((hfun_le y x hy hx).mp h.ge)
  · intro h; rw [h]

lemma nu1 (q y : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hy : y ≠ 0) :
    nu 1 q y = 1 - (y + 1 / y - 2) / Real.log q⁻¹ := by
  unfold nu; rw [c1]
  have hL := L_pos q hq
  simp only [sub_self, Real.rpow_zero, one_mul]
  have : 1 - (1 - y) = y := by ring
  rw [this]
  field_simp; ring

lemma G13_1 (q y : ℝ) : G13 1 q y = Real.log q⁻¹ * y * Real.exp y := by
  unfold G13; rw [c1, GA1]; simp only [vTilde, one_ne_zero, if_false, if_true]
  rw [show -(1 - y) = y + -1 by ring, Real.exp_add]
  have := Real.exp_pos (-1 : ℝ)
  field_simp

lemma G12_1 (q y : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hy : 0 < y) :
    G12 1 q y = Real.exp (-(Real.log q⁻¹) + (1 - y) / y) / y := by
  unfold G12 zf; rw [c1, GA1]
  simp only [sub_self, Real.rpow_zero, one_mul]
  have : 1 - (1 - y) = y := by ring
  rw [this]; congr 2; ring

lemma char_core (u0 : ℝ) (hu0 : u0 ∈ Set.Ioo (1.341 : ℝ) 1.35) (hpsi : psi u0 = 0)
    (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (lambertW (1 / Real.log q⁻¹) * lambertW (Real.exp 1 / q) ≤ 1 ↔ q ≤ Real.exp (-Lf u0)) ∧
    (lambertW (1 / Real.log q⁻¹) * lambertW (Real.exp 1 / q) < 1 ↔ q < Real.exp (-Lf u0)) := by
  obtain ⟨ha, hLeq, hb0, hbe⟩ := q_facts q hq
  set L := Real.log q⁻¹ with hLdef
  set a := lambertW (1 / L)
  set b := lambertW (Real.exp 1 / q)
  set u := a⁻¹ with hu
  have hu0' : 0 < u := inv_pos.mpr ha
  have hu00 : (0 : ℝ) < u0 := by linarith [hu0.1]
  have hq_eq : q = Real.exp (-L) := by rw [hLdef, exp_L q hq.1]
  have hue : u * Real.exp u = Real.exp (Real.log u + u) := by
    rw [Real.exp_add, Real.exp_log hu0']
  have hpsiu : psi u = Real.log u + u - 1 - L := by rw [hLeq]; unfold psi Lf; ring
  constructor
  · calc a * b ≤ 1 ↔ b ≤ u := by
          rw [mul_comm, hu, ← one_div, le_div_iff₀ ha]
      _ ↔ b * Real.exp b ≤ u * Real.exp u :=
          (xexp_strictMono.le_iff_le hb0 (show (0:ℝ) ≤ u from hu0'.le)).symm
      _ ↔ 1 + L ≤ Real.log u + u := by rw [hbe, hue, Real.exp_le_exp]
      _ ↔ psi u0 ≤ psi u := by rw [hpsi, hpsiu]; constructor <;> intro h <;> linarith
      _ ↔ u0 ≤ u := psi_strictMono.le_iff_le hu00 hu0'
      _ ↔ Lf u0 ≤ Lf u := (Lf_strictMono.le_iff_le hu00 hu0').symm
      _ ↔ q ≤ Real.exp (-Lf u0) := by
          rw [← hLeq, hq_eq, Real.exp_le_exp]; constructor <;> intro h <;> linarith
  · calc a * b < 1 ↔ b < u := by
          rw [mul_comm, hu, ← one_div, lt_div_iff₀ ha]
      _ ↔ b * Real.exp b < u * Real.exp u :=
          (xexp_strictMono.lt_iff_lt hb0 (show (0:ℝ) ≤ u from hu0'.le)).symm
      _ ↔ 1 + L < Real.log u + u := by rw [hbe, hue, Real.exp_lt_exp]
      _ ↔ psi u0 < psi u := by rw [hpsi, hpsiu]; constructor <;> intro h <;> linarith
      _ ↔ u0 < u := psi_strictMono.lt_iff_lt hu00 hu0'
      _ ↔ Lf u0 < Lf u := (Lf_strictMono.lt_iff_lt hu00 hu0').symm
      _ ↔ q < Real.exp (-Lf u0) := by
          rw [← hLeq, hq_eq, Real.exp_lt_exp]; constructor <;> intro h <;> linarith

lemma char_eq (u0 : ℝ) (hu0 : u0 ∈ Set.Ioo (1.341 : ℝ) 1.35) (hpsi : psi u0 = 0)
    (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    lambertW (1 / Real.log q⁻¹) * lambertW (Real.exp 1 / q) = 1 ↔ q = Real.exp (-Lf u0) := by
  obtain ⟨h1, h2⟩ := char_core u0 hu0 hpsi q hq
  constructor
  · intro h
    exact le_antisymm (h1.mp h.le) (not_lt.mp (fun hlt => by have := h2.mpr hlt; linarith))
  · intro h
    exact le_antisymm (h1.mpr h.le) (not_lt.mp (fun hlt => by have := h2.mp hlt; linarith))

lemma g_endpoints (q : ℝ) (hq : q = 0 ∨ q = 1) :
    lambertW (1 / Real.log q⁻¹) * lambertW (Real.exp 1 / q) ≠ 1 := by
  rcases hq with h | h <;> subst h <;> simp [W_zero]

lemma qh_bounds (u0 : ℝ) (hu0 : u0 ∈ Set.Ioo (1.341 : ℝ) 1.35) :
    Real.exp (-Lf u0) ∈ Set.Icc (0.52 : ℝ) 0.53 := by
  have h1 : Lf 1.341 < Lf u0 := Lf_strictMono (show (0:ℝ) < 1.341 by norm_num)
    (show (0:ℝ) < u0 by linarith [hu0.1]) hu0.1
  have h2 : Lf u0 < Lf 1.35 := Lf_strictMono (show (0:ℝ) < u0 by linarith [hu0.1])
    (show (0:ℝ) < 1.35 by norm_num) hu0.2
  have l1 := Lf_lo
  have l2 := Lf_hi
  constructor
  · have : Real.exp (-0.6438) ≤ Real.exp (-Lf u0) := Real.exp_le_exp.mpr (by linarith)
    refine le_trans ?_ this
    rw [Real.exp_neg]
    have hm := hM2
    have hp := Real.exp_pos (0.6438 : ℝ)
    rw [le_inv_comm₀ (by norm_num) hp]
    norm_num at hm ⊢; linarith
  · have : Real.exp (-Lf u0) ≤ Real.exp (-0.6361) := Real.exp_le_exp.mpr (by linarith)
    refine le_trans this ?_
    rw [Real.exp_neg]
    have hm := hM1
    have hp := Real.exp_pos (0.6361 : ℝ)
    rw [inv_le_comm₀ hp (by norm_num)]
    norm_num at hm ⊢; linarith

lemma a_le_one (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hqG : q ≤ Real.exp (-Real.exp (-1))) :
    lambertW (1 / Real.log q⁻¹) ≤ 1 := by
  have hL := L_pos q hq
  obtain ⟨ha0, hae⟩ := W_spec (1 / Real.log q⁻¹) (by positivity)
  have hLe : Real.exp (-1) ≤ Real.log q⁻¹ := by
    rw [Real.log_inv]
    have := Real.log_le_log hq.1 hqG
    rw [Real.log_exp] at this; linarith
  by_contra hcon; push Not at hcon
  have h1 : 1 * Real.exp 1 < lambertW (1 / Real.log q⁻¹) * Real.exp (lambertW (1 / Real.log q⁻¹)) :=
    mul_lt_mul hcon (Real.exp_le_exp.mpr hcon.le) (Real.exp_pos _) (by linarith)
  rw [hae, one_mul, lt_div_iff₀ hL] at h1
  have : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos 1]

lemma a_lt_one (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hqG : q < Real.exp (-Real.exp (-1))) :
    lambertW (1 / Real.log q⁻¹) < 1 := by
  have hL := L_pos q hq
  obtain ⟨ha0, hae⟩ := W_spec (1 / Real.log q⁻¹) (by positivity)
  have hLe : Real.exp (-1) < Real.log q⁻¹ := by
    rw [Real.log_inv]
    have := Real.log_lt_log hq.1 hqG
    rw [Real.log_exp] at this; linarith
  by_contra hcon; push Not at hcon
  have h1 : 1 * Real.exp 1 ≤ lambertW (1 / Real.log q⁻¹) * Real.exp (lambertW (1 / Real.log q⁻¹)) :=
    mul_le_mul hcon (Real.exp_le_exp.mpr hcon) (Real.exp_pos _).le (by linarith)
  rw [hae, one_mul, le_div_iff₀ hL] at h1
  have : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos 1]

lemma b_gt_one (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) : 1 < lambertW (Real.exp 1 / q) := by
  obtain ⟨hb0, hbe⟩ := W_spec (Real.exp 1 / q) (by have := hq.1; positivity)
  by_contra hcon; push Not at hcon
  have : lambertW (Real.exp 1 / q) * Real.exp (lambertW (Real.exp 1 / q)) ≤ 1 * Real.exp 1 :=
    mul_le_mul hcon (Real.exp_le_exp.mpr hcon) (Real.exp_pos _).le zero_le_one
  rw [hbe, one_mul, div_le_iff₀ hq.1] at this
  nlinarith [Real.exp_pos 1, hq.2]

lemma b_le (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    lambertW (Real.exp 1 / q) ≤ 1 + Real.log q⁻¹ := by
  obtain ⟨_, _, hb0, hbe⟩ := q_facts q hq
  have hL := L_pos q hq
  by_contra hcon; push Not at hcon
  have h1 : (1 + Real.log q⁻¹) * Real.exp (1 + Real.log q⁻¹) <
      lambertW (Real.exp 1 / q) * Real.exp (lambertW (Real.exp 1 / q)) :=
    xexp_strictMono (show (0:ℝ) ≤ 1 + Real.log q⁻¹ by linarith) hb0 hcon
  rw [hbe] at h1
  have := Real.exp_pos (1 + Real.log q⁻¹)
  nlinarith

theorem part1 :
    ((∃! qh : ℝ, qh ∈ Set.Icc 0 1 ∧
        lambertW (1 / Real.log qh⁻¹) * lambertW (Real.exp 1 / qh) = 1) ∧
      (∀ qh : ℝ, qh ∈ Set.Icc 0 1 →
        lambertW (1 / Real.log qh⁻¹) * lambertW (Real.exp 1 / qh) = 1 →
        qh ∈ Set.Icc (0.52 : ℝ) 0.53 ∧
        qh ∈ Set.Icc (qLow 1) (GammaA 1 (vTilde 1)) ∧
        ∀ q ∈ Set.Icc (qLow 1) (GammaA 1 (vTilde 1)) ∩ Set.Ioo 0 1,
          (betaQ q (1 / Real.log q⁻¹) = betaQ q (Real.exp 1 / q) ↔ q = qh) ∧
          (betaQ q (1 / Real.log q⁻¹) ≤ betaQ q (Real.exp 1 / q) ↔ q ≤ qh)) ∧
      (∀ q ∈ Set.Ico (qLow 1) (GammaA 1 (vTilde 1)) ∩ Set.Ioo 0 1,
        muAQ 1 q (betaQ q (1 / Real.log q⁻¹)) = lambertW (1 / Real.log q⁻¹) ∧
        betaQ q (1 / Real.log q⁻¹) ∈ Set.Icc (rLow 1 1 q) 1 ∧
        (∀ p ∈ Set.Icc (rLow 1 1 q) (betaQ q (1 / Real.log q⁻¹)), R3 1 q p ≤ R1 1 q p) ∧
        (∀ p ∈ Set.Ico (betaQ q (1 / Real.log q⁻¹)) 1, R1 1 q p ≤ R3 1 q p)) ∧
      (∀ q ∈ Set.Ioo (0 : ℝ) 1,
        muAQ 1 q (betaQ q (Real.exp 1 / q)) = 1 / lambertW (Real.exp 1 / q) ∧
        (∀ p ∈ Set.Icc (rLow 1 1 q) (betaQ q (Real.exp 1 / q)), R2 p ≤ R1 1 q p) ∧
        (∀ p ∈ Set.Icc (betaQ q (Real.exp 1 / q)) 1, R1 1 q p ≤ R2 p))) := by
  have hα : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨u0, hu0, hpsi⟩ := psi_root
  set qh0 := Real.exp (-Lf u0) with hqh0
  have hb := qh_bounds u0 hu0
  rw [← hqh0] at hb
  have hqh0I : qh0 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
  -- solutions are exactly qh0
  have hsol : ∀ y : ℝ, y ∈ Set.Icc 0 1 →
      (lambertW (1 / Real.log y⁻¹) * lambertW (Real.exp 1 / y) = 1 ↔ y = qh0) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h0 | h0
    · subst h0
      exact ⟨fun h => absurd h (g_endpoints 0 (Or.inl rfl)), fun h => by linarith [hqh0I.1]⟩
    rcases eq_or_lt_of_le hy.2 with h1 | h1
    · subst h1
      exact ⟨fun h => absurd h (g_endpoints 1 (Or.inr rfl)), fun h => by linarith [hqh0I.2]⟩
    exact char_eq u0 hu0 hpsi y ⟨h0, h1⟩
  have hGv : (0.53 : ℝ) < GammaA 1 (vTilde 1) := by rw [GV1]; exact exp_neg_exp_gt
  have hql : qLow 1 < 0.52 := by
    rw [qLow1]
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    norm_num; linarith
  refine ⟨⟨qh0, ⟨⟨hqh0I.1.le, hqh0I.2.le⟩, (hsol qh0 ⟨hqh0I.1.le, hqh0I.2.le⟩).mpr rfl⟩,
    fun y ⟨hy, heq⟩ => (hsol y hy).mp heq⟩, ?_, ?_, ?_⟩
  · intro qh hqh heq
    have hq0 : qh = qh0 := (hsol qh hqh).mp heq
    subst hq0
    refine ⟨hb, ⟨by linarith [hb.1], by linarith [hb.2]⟩, ?_⟩
    rintro q ⟨⟨hqL, hqG⟩, hq⟩
    rw [GV1] at hqG
    have hL := L_pos q hq
    obtain ⟨ha, _, _, _⟩ := q_facts q hq
    have ha1 := a_le_one q hq hqG
    have hb1 := b_gt_one q hq
    set a := lambertW (1 / Real.log q⁻¹)
    set b := lambertW (Real.exp 1 / q)
    have hia : 1 ≤ 1 / a := by rw [le_div_iff₀ ha]; linarith
    have hsym : a + 1 / a = 1 / a + 1 / (1 / a) := by rw [one_div_one_div]; ring
    have hβle : betaQ q (1 / Real.log q⁻¹) ≤ betaQ q (Real.exp 1 / q) ↔ b + 1 / b ≤ a + 1 / a := by
      unfold betaQ
      rw [← show lambertW (1 / Real.log q⁻¹) = a from rfl,
        ← show lambertW (Real.exp 1 / q) = b from rfl, sub_le_sub_iff_left,
        div_le_div_iff_of_pos_right hL]
      constructor <;> intro h <;> linarith
    have hβeq : betaQ q (1 / Real.log q⁻¹) = betaQ q (Real.exp 1 / q) ↔ b + 1 / b = a + 1 / a := by
      unfold betaQ
      rw [← show lambertW (1 / Real.log q⁻¹) = a from rfl,
        ← show lambertW (Real.exp 1 / q) = b from rfl]
      constructor
      · intro h
        have : (a + 1 / a - 2) / Real.log q⁻¹ = (b + 1 / b - 2) / Real.log q⁻¹ := by linarith
        rw [div_left_inj' hL.ne'] at this; linarith
      · intro h; rw [show a + 1 / a - 2 = b + 1 / b - 2 by linarith]
    have hcc := char_core u0 hu0 hpsi q hq
    have hce := char_eq u0 hu0 hpsi q hq
    have hab : a * b ≤ 1 ↔ b ≤ 1 / a := by rw [mul_comm, le_div_iff₀ ha]
    have habe : a * b = 1 ↔ b = 1 / a := by
      rw [eq_div_iff ha.ne', mul_comm]
    refine ⟨?_, ?_⟩
    · rw [hβeq, hsym, hfun_eq b (1 / a) hb1.le hia, ← habe]; exact hce
    · rw [hβle, hsym, hfun_le b (1 / a) hb1.le hia, ← hab]; exact hcc.1
  · rintro q ⟨⟨hqL, hqG⟩, hq⟩
    rw [GV1] at hqG
    rw [qLow1] at hqL
    have hL := L_pos q hq
    obtain ⟨ha, _, _, _⟩ := q_facts q hq
    obtain ⟨_, hae⟩ := W_spec (1 / Real.log q⁻¹) (by positivity)
    set y := lambertW (1 / Real.log q⁻¹) with hy
    have hy1 := a_lt_one q hq hqG
    have hG : G13 1 q y = 1 := by
      rw [G13_1, mul_assoc, hae, mul_one_div_cancel hL.ne']
    have hyL : rLow 1 1 q ≤ y := by
      by_contra hcon; push Not at hcon
      have h1 := G13_rLow 1 q hα hq
      rw [G13_1] at h1
      have hr0 := rLow_pos 1 q hα hq
      have : Real.log q⁻¹ * y * Real.exp y < Real.log q⁻¹ * rLow 1 1 q * Real.exp (rLow 1 1 q) := by
        have := xexp_strictMono (show (0:ℝ) ≤ y from ha.le) (show (0:ℝ) ≤ rLow 1 1 q from hr0.le) hcon
        simp only at this
        nlinarith
      rw [G13_1] at hG
      linarith
    have hyI : y ∈ Set.Icc (rLow 1 1 q) 1 := ⟨hyL, hy1.le⟩
    have hc := cross13 1 q y hα hq (by rw [qLow1]; exact hqL) hyI hy1 hG
    rw [nu1 q y hq ha.ne'] at hc
    have hbeta : betaQ q (1 / Real.log q⁻¹) = 1 - (y + 1 / y - 2) / Real.log q⁻¹ := by
      unfold betaQ; rw [← hy]
    rw [hbeta]
    refine ⟨?_, hc⟩
    have := mu_nu 1 q y hα hq hyI
    rw [nu1 q y hq ha.ne'] at this
    exact this
  · intro q hq
    have hL := L_pos q hq
    obtain ⟨_, _, hb0, hbe⟩ := q_facts q hq
    have hb1 := b_gt_one q hq
    have hbL := b_le q hq
    set b := lambertW (Real.exp 1 / q) with hbdef
    have hb0' : 0 < b := by linarith
    set y := 1 / b with hy
    have hy0 : 0 < y := by positivity
    have hy1 : y < 1 := by rw [hy, div_lt_one hb0']; exact hb1
    have hyL : rLow 1 1 q ≤ y := by
      rw [rLow1, hy]; exact one_div_le_one_div_of_le hb0' (by linarith)
    have hyI : y ∈ Set.Icc (rLow 1 1 q) 1 := ⟨hyL, hy1.le⟩
    have hG : G12 1 q y = 1 := by
      rw [G12_1 q y hq hy0]
      have e1 : (1 - y) / y = b - 1 := by rw [hy]; field_simp
      rw [e1, hy, div_div_eq_mul_div, div_one, show -Real.log q⁻¹ + (b - 1) = b - (1 + Real.log q⁻¹) by ring,
        Real.exp_sub, ← hbe]
      field_simp
    have hc := cross12 1 q y hα hq hyI hy1 hG
    have hnu : nu 1 q y = betaQ q (Real.exp 1 / q) := by
      rw [nu1 q y hq hy0.ne']; unfold betaQ; rw [← hbdef, hy, one_div_one_div]; ring
    rw [hnu] at hc
    refine ⟨?_, hc⟩
    have := mu_nu 1 q y hα hq hyI
    rw [hnu] at this
    exact this

end SPPL2

open SinglePointPricing.Det in
theorem solution :
    ((1 / 4 : ℝ) ∈ Set.Icc (qLow 0) (GammaA 0 (vTilde 0)) ∩ Set.Ioo 0 1 ∧
      (∀ q ∈ Set.Icc (qLow 0) (GammaA 0 (vTilde 0)) ∩ Set.Ioo 0 1,
        (1 - (1 - 2 * q) ^ 2 / (1 - q) = 1 - (1 - Real.sqrt q) ^ 2 / (1 - q) ↔ q = 1 / 4) ∧
        (1 - (1 - 2 * q) ^ 2 / (1 - q) ≤ 1 - (1 - Real.sqrt q) ^ 2 / (1 - q) ↔ q ≤ 1 / 4)) ∧
      (∀ q ∈ Set.Ico (qLow 0) (GammaA 0 (vTilde 0)) ∩ Set.Ioo 0 1,
        1 - (1 - 2 * q) ^ 2 / (1 - q) ∈ Set.Icc (rLow 0 1 q) 1 ∧
        (∀ p ∈ Set.Icc (rLow 0 1 q) (1 - (1 - 2 * q) ^ 2 / (1 - q)), R3 0 q p ≤ R1 0 q p) ∧
        (∀ p ∈ Set.Ico (1 - (1 - 2 * q) ^ 2 / (1 - q)) 1, R1 0 q p ≤ R3 0 q p)) ∧
      (∀ q ∈ Set.Ioo (0 : ℝ) 1,
        (∀ p ∈ Set.Icc (rLow 0 1 q) (1 - (1 - Real.sqrt q) ^ 2 / (1 - q)), R2 p ≤ R1 0 q p) ∧
        (∀ p ∈ Set.Icc (1 - (1 - Real.sqrt q) ^ 2 / (1 - q)) 1, R1 0 q p ≤ R2 p))) ∧
    ((∃! qh : ℝ, qh ∈ Set.Icc 0 1 ∧
        lambertW (1 / Real.log qh⁻¹) * lambertW (Real.exp 1 / qh) = 1) ∧
      (∀ qh : ℝ, qh ∈ Set.Icc 0 1 →
        lambertW (1 / Real.log qh⁻¹) * lambertW (Real.exp 1 / qh) = 1 →
        qh ∈ Set.Icc (0.52 : ℝ) 0.53 ∧
        qh ∈ Set.Icc (qLow 1) (GammaA 1 (vTilde 1)) ∧
        ∀ q ∈ Set.Icc (qLow 1) (GammaA 1 (vTilde 1)) ∩ Set.Ioo 0 1,
          (betaQ q (1 / Real.log q⁻¹) = betaQ q (Real.exp 1 / q) ↔ q = qh) ∧
          (betaQ q (1 / Real.log q⁻¹) ≤ betaQ q (Real.exp 1 / q) ↔ q ≤ qh)) ∧
      (∀ q ∈ Set.Ico (qLow 1) (GammaA 1 (vTilde 1)) ∩ Set.Ioo 0 1,
        muAQ 1 q (betaQ q (1 / Real.log q⁻¹)) = lambertW (1 / Real.log q⁻¹) ∧
        betaQ q (1 / Real.log q⁻¹) ∈ Set.Icc (rLow 1 1 q) 1 ∧
        (∀ p ∈ Set.Icc (rLow 1 1 q) (betaQ q (1 / Real.log q⁻¹)), R3 1 q p ≤ R1 1 q p) ∧
        (∀ p ∈ Set.Ico (betaQ q (1 / Real.log q⁻¹)) 1, R1 1 q p ≤ R3 1 q p)) ∧
      (∀ q ∈ Set.Ioo (0 : ℝ) 1,
        muAQ 1 q (betaQ q (Real.exp 1 / q)) = 1 / lambertW (Real.exp 1 / q) ∧
        (∀ p ∈ Set.Icc (rLow 1 1 q) (betaQ q (Real.exp 1 / q)), R2 p ≤ R1 1 q p) ∧
        (∀ p ∈ Set.Icc (betaQ q (Real.exp 1 / q)) 1, R1 1 q p ≤ R2 p))) :=
  ⟨SPPL2.part0, SPPL2.part1⟩
