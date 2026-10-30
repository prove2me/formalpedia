-- Prove2me | solution 1 for SinglePointPricing.Det.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T09:45:28.699512+00:00
-- url     : https://prove2.me/submissions/67259f0f-4a3e-4749-8239-fb4383dde50f

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase
import Theorems.Thm_SinglePointPricing_Det_theorem_1
import Theorems.Thm_SinglePointPricing_Det_lemma_C_2
import Theorems.Thm_SinglePointPricing_Det_propD1_worst_terms
import Theorems.Thm_SinglePointPricing_Det_proposition_D_1
import Theorems.Thm_SinglePointPricing_Det_lemma_D_1
import Theorems.Thm_SinglePointPricing_Det_lemma_D_2

namespace SPPT2
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

/-! Abstract sup-of-min computations. -/

lemma low3 (f1 f2 f3 : ℝ → ℝ) (a p12 p13 : ℝ) (ha : 0 ≤ a) (h12a : a ≤ p12) (h12 : p12 < 1)
    (h1312 : p13 ≤ p12) (hf2 : ∀ p, p ≤ 1 → f2 p = p) (hf1c : f1 p12 = p12)
    (hf1anti : AntitoneOn f1 (Set.Ico a 1)) (hf31 : ∀ p ∈ Set.Ico p13 1, f1 p ≤ f3 p) :
    IsGreatest ((fun p => min (f1 p) (min (f2 p) (f3 p))) '' Set.Ico 0 1) p12 ∧
      min (f1 p12) (min (f2 p12) (f3 p12)) = p12 := by
  have hv : min (f1 p12) (min (f2 p12) (f3 p12)) = p12 := by
    have h3 := hf31 p12 ⟨h1312, h12⟩
    rw [hf2 p12 h12.le, hf1c]
    rw [hf1c] at h3
    simp [h3]
  refine ⟨⟨⟨p12, ⟨le_trans ha h12a, h12⟩, hv⟩, ?_⟩, hv⟩
  · rintro _ ⟨p, hp, rfl⟩
    simp only
    by_cases hpp : p ≤ p12
    · exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (by rw [hf2 p hp.2.le]; exact hpp))
    · push Not at hpp
      have := hf1anti ⟨h12a, h12⟩ ⟨by linarith, hp.2⟩ hpp.le
      rw [hf1c] at this
      exact le_trans (min_le_left _ _) this

lemma low2 (f1 f2 : ℝ → ℝ) (a p12 : ℝ) (ha : 0 ≤ a) (h12a : a ≤ p12) (h12 : p12 < 1)
    (hf2 : ∀ p, p ≤ 1 → f2 p = p) (hf1c : f1 p12 = p12)
    (hf1anti : AntitoneOn f1 (Set.Ico a 1)) :
    IsGreatest ((fun p => min (f1 p) (f2 p)) '' Set.Ico 0 1) p12 ∧
      min (f1 p12) (f2 p12) = p12 := by
  have hv : min (f1 p12) (f2 p12) = p12 := by rw [hf2 p12 h12.le, hf1c, min_self]
  refine ⟨⟨⟨p12, ⟨le_trans ha h12a, h12⟩, hv⟩, ?_⟩, hv⟩
  · rintro _ ⟨p, hp, rfl⟩
    simp only
    by_cases hpp : p ≤ p12
    · exact le_trans (min_le_right _ _) (by rw [hf2 p hp.2.le]; exact hpp)
    · push Not at hpp
      have := hf1anti ⟨h12a, h12⟩ ⟨by linarith, hp.2⟩ hpp.le
      rw [hf1c] at this
      exact le_trans (min_le_left _ _) this

lemma mid3 (f1 f2 f3 : ℝ → ℝ) (a p12 p13 : ℝ) (ha : 0 ≤ a) (h13a : a ≤ p13) (h13 : p13 < 1)
    (hf3mono : MonotoneOn f3 (Set.Icc 0 1)) (hf1anti : AntitoneOn f1 (Set.Ico a 1))
    (hcross : f1 p13 = f3 p13) (hf21 : f1 p13 ≤ f2 p13) :
    IsGreatest ((fun p => min (f1 p) (min (f2 p) (f3 p))) '' Set.Ico 0 1) (f3 p13) ∧
      min (f1 p13) (min (f2 p13) (f3 p13)) = f3 p13 := by
  have hv : min (f1 p13) (min (f2 p13) (f3 p13)) = f3 p13 := by
    rw [hcross] at hf21 ⊢
    rw [min_eq_right hf21, min_self]
  refine ⟨⟨⟨p13, ⟨le_trans ha h13a, h13⟩, hv⟩, ?_⟩, hv⟩
  · rintro _ ⟨p, hp, rfl⟩
    simp only
    by_cases hpp : p ≤ p13
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (hf3mono ⟨hp.1, hp.2.le⟩ ⟨le_trans ha h13a, h13.le⟩ hpp))
    · push Not at hpp
      have := hf1anti ⟨h13a, h13⟩ ⟨by linarith, hp.2⟩ hpp.le
      rw [hcross] at this
      exact le_trans (min_le_left _ _) this

lemma high3 (f1 f2 f3 : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (hf3mono : MonotoneOn f3 (Set.Icc 0 1)) (hf3cont : ContinuousWithinAt f3 (Set.Icc 0 1) 1)
    (hf2 : ∀ p, p ≤ 1 → f2 p = p) (hf13 : ∀ p ∈ Set.Ico a 1, f3 p ≤ f1 p) (hf31 : f3 1 ≤ 1) :
    IsLUB ((fun p => min (f1 p) (min (f2 p) (f3 p))) '' Set.Ico 0 1) (f3 1) := by
  constructor
  · rintro _ ⟨p, hp, rfl⟩
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (hf3mono ⟨hp.1, hp.2.le⟩ ⟨zero_le_one, le_rfl⟩ hp.2.le))
  · intro b hb
    by_contra hcon; push Not at hcon
    rw [Metric.continuousWithinAt_iff] at hf3cont
    obtain ⟨δ, hδ, hball⟩ := hf3cont (f3 1 - b) (by linarith)
    set m := max a (max b (1 - δ / 2)) with hm
    have hm1 : m < 1 := max_lt ha1 (max_lt (by linarith) (by linarith))
    set p := (m + 1) / 2 with hp
    have hpm : m < p := by rw [hp]; linarith
    have hp1 : p < 1 := by rw [hp]; linarith
    have hap : a < p := lt_of_le_of_lt (le_max_left _ _) hpm
    have hbp : b < p := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hpm
    have hδp : 1 - δ / 2 < p := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hpm
    have hdist : dist p 1 < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have h3 := hball ⟨by linarith, hp1.le⟩ hdist
    rw [Real.dist_eq, abs_lt] at h3
    have hf3p : b < f3 p := by linarith [h3.1]
    have hmem : min (f1 p) (min (f2 p) (f3 p)) ∈
        ((fun p => min (f1 p) (min (f2 p) (f3 p))) '' Set.Ico 0 1) :=
      ⟨p, ⟨by linarith, hp1⟩, rfl⟩
    have hle := hb hmem
    have h1 := hf13 p ⟨hap.le, hp1⟩
    rw [hf2 p hp1.le] at hle
    have : b < min (f1 p) (min p (f3 p)) := lt_min (by linarith) (lt_min hbp hf3p)
    linarith

lemma pack (α w q V x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hval : maximin Pd (FClass α w q) = V) (hV : 0 < V)
    (hx : 0 ≤ x)
    (hlow : ∀ r' ∈ rSet α 1 q, V ≤ x * Fbar α 1 q r' x / optFun (Fbar α 1 q r')) :
    sInf (ratio (Measure.dirac (w * x)) '' FClass α w q) = maximin Pd (FClass α w q) := by
  have hS := S_nonempty α w q hα hw hq (hval ▸ hV)
  apply le_antisymm (inner_le α w q (w * x) hα hw hq (by positivity) hS)
  rw [hval]; exact inner_ge α w q x V hα hw hq hx hS hlow

/-! ## The regular case `α = 0`. -/

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

theorem regular (w q : ℝ) (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    maximin Pd (FClass 0 w q) =
          2 * Real.sqrt q / (1 + Real.sqrt q) * (Set.Ioc (0 : ℝ) (1 / 4)).indicator 1 q
          + (3 - 4 * q) / (4 * (1 - q)) * (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator 1 q
          + (1 - q) * (Set.Ioo (1 / 2 : ℝ) 1).indicator 1 q ∧
      0 ≤ w * (2 * Real.sqrt q / (1 + Real.sqrt q) * (Set.Ioc (0 : ℝ) (1 / 4)).indicator 1 q
          + q * (3 - 4 * q) / (1 - q) * (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator 1 q
          + (Set.Ioo (1 / 2 : ℝ) 1).indicator 1 q) ∧
      sInf (ratio (Measure.dirac
          (w * (2 * Real.sqrt q / (1 + Real.sqrt q) * (Set.Ioc (0 : ℝ) (1 / 4)).indicator 1 q
            + q * (3 - 4 * q) / (1 - q) * (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator 1 q
            + (Set.Ioo (1 / 2 : ℝ) 1).indicator 1 q))) '' FClass 0 w q) =
        maximin Pd (FClass 0 w q) := by
  have hα : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨hq0, hq1⟩ := hq
  have hc := GAInv_pos 0 q hα ⟨hq0, hq1⟩
  have hqL : qLow 0 ≤ q := by rw [qLow0]; exact hq0.le
  have hval3 := (proposition_D_1 0 hα w hw q ⟨hq0, hq1⟩).1 hqL
  have d1 := lemma_D_1 0 hα q ⟨hq0, hq1⟩
  have hanti := (d1.2.2.2 (Or.inl rfl)).1
  obtain ⟨_, hiff, hp13, hp12⟩ := lemma_D_2.1
  have hr : rLow 0 1 q = q := rLow0 q hq0
  have hf2 : ∀ p : ℝ, p ≤ 1 → R2 p = p := fun p hp => R2_eq p hp
  have h1q : 0 < 1 - q := by linarith
  set P12 := 1 - (1 - Real.sqrt q) ^ 2 / (1 - q) with hP12
  set P13 := 1 - (1 - 2 * q) ^ 2 / (1 - q) with hP13
  set t := Real.sqrt q with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hq0
  have ht2 : t ^ 2 = q := Real.sq_sqrt hq0.le
  have ht1 : t < 1 := by nlinarith
  have hP12e : P12 = 2 * t / (1 + t) := by
    rw [hP12, ← ht2]
    have : 1 - t ^ 2 ≠ 0 := by nlinarith
    field_simp; ring
  have hP12q : q ≤ P12 := by
    rw [hP12e, le_div_iff₀ (by linarith), ← ht2]; nlinarith [mul_pos ht0 (sub_pos.mpr ht1)]
  have hP12_1 : P12 < 1 := by rw [hP12e, div_lt_one (by linarith)]; linarith
  have hcross12 : R1 0 q P12 = P12 := by
    have a1 := (hp12 q ⟨hq0, hq1⟩).1 P12 ⟨by rw [hr]; exact hP12q, le_rfl⟩
    have a2 := (hp12 q ⟨hq0, hq1⟩).2 P12 ⟨le_rfl, hP12_1.le⟩
    rw [hf2 P12 hP12_1.le] at a1 a2
    linarith
  have hP12pos : 0 < P12 := lt_of_lt_of_le hq0 hP12q
  rcases le_or_gt q (1 / 4) with hA | hBC
  · -- low region
    have h1312 : P13 ≤ P12 :=
      ((hiff q ⟨⟨hqL, by rw [GV0]; linarith⟩, ⟨hq0, hq1⟩⟩).2).mpr hA
    have hq13 := hp13 q ⟨⟨hqL, by rw [GV0]; linarith⟩, ⟨hq0, hq1⟩⟩
    obtain ⟨LG, Lv⟩ := low3 (R1 0 q) R2 (R3 0 q) (rLow 0 1 q) P12 P13 (by rw [hr]; exact hq0.le)
      (by rw [hr]; exact hP12q) hP12_1 h1312 hf2 hcross12 hanti hq13.2.2
    have hval : maximin Pd (FClass 0 w q) = P12 := by rw [hval3, LG.csSup_eq]
    have hi1 : (Set.Ioc (0 : ℝ) (1 / 4)).indicator (1 : ℝ → ℝ) q = 1 := by
      rw [Set.indicator_of_mem (show q ∈ Set.Ioc (0 : ℝ) (1 / 4) from ⟨hq0, hA⟩)]; rfl
    have hi2 : (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator (1 : ℝ → ℝ) q = 0 :=
      Set.indicator_of_notMem (fun h => by linarith [h.1]) _
    have hi3 : (Set.Ioo (1 / 2 : ℝ) 1).indicator (1 : ℝ → ℝ) q = 0 :=
      Set.indicator_of_notMem (fun h => by linarith [h.1]) _
    rw [hi1, hi2, hi3]
    have e : 2 * t / (1 + t) * 1 + q * (3 - 4 * q) / (1 - q) * 0 + 0 = P12 := by
      rw [hP12e]; ring
    have e' : 2 * t / (1 + t) * 1 + (3 - 4 * q) / (4 * (1 - q)) * 0 + (1 - q) * 0 = P12 := by
      rw [hP12e]; ring
    rw [e, e', hval]
    refine ⟨rfl, by positivity, ?_⟩
    refine (pack 0 w q P12 P12 hα hw ⟨hq0, hq1⟩ hval hP12pos hP12pos.le ?_).trans hval
    intro r' hr'
    have := (lowbound 0 q P12 hα ⟨hq0, hq1⟩ ⟨by rw [hr]; exact hP12q, hP12_1⟩ r' hr').1 hqL
    rwa [Lv] at this
  · rcases lt_or_ge q (1 / 2) with hB | hC
    · -- middle region
      have hq13 := hp13 q ⟨⟨hqL, by rw [GV0]; exact hB⟩, ⟨hq0, hq1⟩⟩
      have h1213 : P12 ≤ P13 := by
        have := mt ((hiff q ⟨⟨hqL, by rw [GV0]; linarith⟩, ⟨hq0, hq1⟩⟩).2).mp (by linarith)
        exact le_of_lt (not_le.mp this)
      have hP13_1 : P13 < 1 := by
        rw [hP13]
        have : 0 < (1 - 2 * q) ^ 2 / (1 - q) := div_pos (by nlinarith) h1q
        linarith
      have hP13r := hq13.1.1
      have hcross : R1 0 q P13 = R3 0 q P13 := by
        have a1 := hq13.2.1 P13 ⟨hP13r, le_rfl⟩
        have a2 := hq13.2.2 P13 ⟨le_rfl, hP13_1⟩
        linarith
      have hf21 : R1 0 q P13 ≤ R2 P13 := (hp12 q ⟨hq0, hq1⟩).2 P13 ⟨h1213, hP13_1.le⟩
      obtain ⟨LG, Lv⟩ := mid3 (R1 0 q) R2 (R3 0 q) (rLow 0 1 q) P12 P13
        (by rw [hr]; exact hq0.le) hP13r hP13_1 (R3_0_mono q ⟨hq0, hq1⟩) hanti hcross hf21
      have hV : R3 0 q P13 = (3 - 4 * q) / (4 * (1 - q)) := by
        have hcP : (1 / q - 1) * P13 = 3 - 4 * q := by
          rw [hP13]
          have : q ≠ 0 := hq0.ne'
          have : (1 : ℝ) - q ≠ 0 := by linarith
          field_simp; ring
        rw [R3_0, c0, hcP]; congr 1; ring
      have hP13e : P13 = q * (3 - 4 * q) / (1 - q) := by
        rw [hP13]; field_simp; ring
      have hval : maximin Pd (FClass 0 w q) = (3 - 4 * q) / (4 * (1 - q)) := by
        rw [hval3, LG.csSup_eq, hV]
      have hVpos : 0 < (3 - 4 * q) / (4 * (1 - q)) := div_pos (by linarith) (by linarith)
      have hi1 : (Set.Ioc (0 : ℝ) (1 / 4)).indicator (1 : ℝ → ℝ) q = 0 :=
        Set.indicator_of_notMem (fun h => by linarith [h.2]) _
      have hi2 : (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator (1 : ℝ → ℝ) q = 1 := by
        rw [Set.indicator_of_mem (show q ∈ Set.Ioc (1 / 4 : ℝ) (1 / 2) from ⟨hBC, hB.le⟩)]; rfl
      have hi3 : (Set.Ioo (1 / 2 : ℝ) 1).indicator (1 : ℝ → ℝ) q = 0 :=
        Set.indicator_of_notMem (fun h => by linarith [h.1]) _
      rw [hi1, hi2, hi3]
      have e : 2 * t / (1 + t) * 0 + q * (3 - 4 * q) / (1 - q) * 1 + 0 = P13 := by
        rw [hP13e]; ring
      have e' : 2 * t / (1 + t) * 0 + (3 - 4 * q) / (4 * (1 - q)) * 1 + (1 - q) * 0
          = (3 - 4 * q) / (4 * (1 - q)) := by ring
      have hP13pos : 0 < P13 := lt_of_lt_of_le (rLow_pos 0 q hα ⟨hq0, hq1⟩) hP13r
      rw [e, e', hval]
      refine ⟨rfl, by positivity, ?_⟩
      refine (pack 0 w q _ P13 hα hw ⟨hq0, hq1⟩ hval hVpos hP13pos.le ?_).trans hval
      intro r' hr'
      have := (lowbound 0 q P13 hα ⟨hq0, hq1⟩ ⟨hP13r, hP13_1⟩ r' hr').1 hqL
      rwa [Lv, hV] at this
    · -- high region
      have hf13 : ∀ p ∈ Set.Ico (rLow 0 1 q) 1, R3 0 q p ≤ R1 0 q p := fun p hp =>
        d1.1.2 ⟨by rw [GV0]; exact hC, hq1.le⟩ p ⟨hp.1, hp.2.le⟩
      have hR31 : R3 0 q 1 = 1 - q := by
        rw [R3_0, c0]; field_simp; ring
      have hLUB := high3 (R1 0 q) R2 (R3 0 q) (rLow 0 1 q) (by rw [hr]; exact hq0.le)
        (by rw [hr]; exact hq1) (R3_0_mono q ⟨hq0, hq1⟩) (R3_0_cont q ⟨hq0, hq1⟩) hf2 hf13
        (by rw [hR31]; linarith)
      have hne : ((fun p => min (R1 0 q p) (min (R2 p) (R3 0 q p))) '' Set.Ico 0 1).Nonempty :=
        ⟨_, 0, ⟨le_rfl, zero_lt_one⟩, rfl⟩
      have hval : maximin Pd (FClass 0 w q) = 1 - q := by
        rw [hval3, hLUB.csSup_eq hne, hR31]
      have hlow : ∀ r' ∈ rSet 0 1 q, 1 - q ≤ 1 * Fbar 0 1 q r' 1 / optFun (Fbar 0 1 q r') := by
        intro r' hr'
        have := lowbound_one 0 q hα ⟨hq0, hq1⟩ hqL r' hr'
        rw [hR31, min_eq_right (by linarith)] at this
        exact this
      have hfin := pack 0 w q (1 - q) 1 hα hw ⟨hq0, hq1⟩ hval (by linarith) zero_le_one hlow
      have hi1 : (Set.Ioc (0 : ℝ) (1 / 4)).indicator (1 : ℝ → ℝ) q = 0 :=
        Set.indicator_of_notMem (fun h => by linarith [h.2]) _
      rw [hi1]
      rcases eq_or_lt_of_le hC with hE | hD
      · -- q = 1/2
        have hi2 : (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator (1 : ℝ → ℝ) q = 1 := by
          rw [Set.indicator_of_mem (show q ∈ Set.Ioc (1 / 4 : ℝ) (1 / 2) from
            ⟨by linarith, hE.symm.le⟩)]; rfl
        have hi3 : (Set.Ioo (1 / 2 : ℝ) 1).indicator (1 : ℝ → ℝ) q = 0 :=
          Set.indicator_of_notMem (fun h => by linarith [h.1]) _
        rw [hi2, hi3, ← hE]
        rw [← hE] at hval hfin
        norm_num at hval hfin ⊢
        refine ⟨hval, by positivity, ?_⟩
        exact hfin
      · have hi2 : (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator (1 : ℝ → ℝ) q = 0 :=
          Set.indicator_of_notMem (fun h => by linarith [h.2]) _
        have hi3 : (Set.Ioo (1 / 2 : ℝ) 1).indicator (1 : ℝ → ℝ) q = 1 := by
          rw [Set.indicator_of_mem (show q ∈ Set.Ioo (1 / 2 : ℝ) 1 from ⟨hD, hq1⟩)]; rfl
        rw [hi2, hi3]
        simp only [mul_zero, mul_one, zero_add]
        exact ⟨hval, hw.le, by simpa using hfin⟩

/-! ## The mhr case `α = 1`. -/

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

noncomputable def R3e (L p : ℝ) : ℝ := Real.exp 1 * L * p * Real.exp (-(L * p))

lemma R3_1 (q p : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hqL : Real.exp (-1) ≤ q)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) : R3 1 q p = R3e (Real.log q⁻¹) p := by
  have hα : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hL := L_pos q hq
  have hL1 := L_le_one q hq hqL
  set L := Real.log q⁻¹ with hLdef
  have hrb : 1 ≤ 1 / (1 * L) := by rw [one_mul, le_div_iff₀ hL]; linarith
  have hrb2 : 1 * GammaAInv 1 q * (1 / (1 * L)) ≤ 1 := by
    rw [c1, ← hLdef]; field_simp; rfl
  have hR : R3 1 q p = p * Fbar 1 1 q (1 / (1 * L)) p / optFun (Fbar 1 1 q (1 / (1 * L))) := by
    simp [R3, c1, ← hLdef]
  rw [hR, optFun_rw 1 1 q _ hα one_pos hq (Or.inr ⟨hrb, hrb2⟩),
    Fbar_ge 1 q _ p hrb hp.1 (le_trans hp.2 hrb), Fbar_ge 1 q _ _ hrb (by linarith) le_rfl,
    GA1, GA1, c1, ← hLdef]
  unfold R3e
  have : L * (1 / (1 * L)) = 1 := by field_simp
  rw [this]
  have he : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
  rw [he]
  field_simp

lemma R3e_mono (L : ℝ) (hL : 0 < L) (hL1 : L ≤ 1) : MonotoneOn (R3e L) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  unfold R3e
  have hk : 0 < Real.exp 1 * L := by positivity
  rw [mul_assoc (Real.exp 1 * L), mul_assoc (Real.exp 1 * L)]
  apply mul_le_mul_of_nonneg_left _ hk.le
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · rw [← h0]; simp; exact mul_nonneg hy.1 (Real.exp_pos _).le
  · have hy0 : 0 < y := lt_of_lt_of_le h0 hxy
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul h0.ne' (by positivity),
      Real.log_mul hy0.ne' (by positivity), Real.log_exp, Real.log_exp]
    have h1 := Real.log_le_sub_one_of_pos (div_pos h0 hy0)
    rw [Real.log_div h0.ne' hy0.ne'] at h1
    have h2 : x / y - 1 ≤ L * (x - y) := by
      rw [div_sub_one hy0.ne', div_le_iff₀ hy0]
      nlinarith [mul_le_mul_of_nonneg_left hy.2 hL.le]
    linarith

lemma R3e_cont (L : ℝ) : Continuous (R3e L) := by unfold R3e; fun_prop

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

/-- the low-regime price `β_q(e/q)` lies in `[r̲_1(1,q), 1)`. -/
lemma beta_eq_facts (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    rLow 1 1 q ≤ betaQ q (Real.exp 1 / q) ∧ betaQ q (Real.exp 1 / q) < 1 := by
  have hL := L_pos q hq
  obtain ⟨hW0, hWe⟩ := W_spec (Real.exp 1 / q) (by have := hq.1; positivity)
  set W := lambertW (Real.exp 1 / q) with hWdef
  set L := Real.log q⁻¹ with hLdef
  have hW1 : 1 < W := by
    by_contra hcon; push Not at hcon
    have : W * Real.exp W ≤ 1 * Real.exp 1 := by
      apply mul_le_mul hcon (Real.exp_le_exp.mpr hcon) (Real.exp_pos _).le zero_le_one
    rw [hWe, one_mul, div_le_iff₀ hq.1] at this
    have := Real.exp_pos 1
    nlinarith [hq.2]
  have hW0' : 0 < W := by linarith
  have hlog : Real.log W + W = 1 + L := by
    have := congrArg Real.log hWe
    rw [Real.log_mul hW0'.ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_div (Real.exp_pos _).ne' hq.1.ne', Real.log_exp] at this
    rw [hLdef, Real.log_inv]; linarith
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg hW1.le
  unfold betaQ
  rw [← hWdef, ← hLdef, rLow1, ← hLdef]
  have e : W + 1 / W - 2 = (W - 1) ^ 2 / W := by field_simp; ring
  rw [e]
  constructor
  · rw [div_div, sub_eq_add_neg, le_add_neg_iff_add_le, ← sub_nonneg]
    have hcalc : 1 - 1 / (L + 1) - (W - 1) ^ 2 / (W * L)
        = (W * L ^ 2 - (W - 1) ^ 2 * (L + 1)) / (W * L * (L + 1)) := by
      field_simp; ring
    have : 1 / (L + 1) + (W - 1) ^ 2 / (W * L) ≤ 1 := by
      have hnum : 0 ≤ W * L ^ 2 - (W - 1) ^ 2 * (L + 1) := by
        have hLa : W - 1 ≤ L := by linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hLa) (by linarith : (0 : ℝ) ≤ L + (W - 1)),
          mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ W - 1) hL.le) (sub_nonneg.mpr hLa)]
      have : 0 ≤ (W * L ^ 2 - (W - 1) ^ 2 * (L + 1)) / (W * L * (L + 1)) :=
        div_nonneg hnum (by positivity)
      linarith
    linarith
  · have : 0 < (W - 1) ^ 2 / W / L := by
      apply div_pos (div_pos (by nlinarith) hW0') hL
    linarith

theorem mhr (qh : ℝ) (hqh : qh ∈ Set.Icc 0 1)
    (heq : lambertW (1 / Real.log qh⁻¹) * lambertW (Real.exp 1 / qh) = 1)
    (w q : ℝ) (hw : 0 < w) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
        maximin Pd (FClass 1 w q) =
            betaQ q (Real.exp 1 / q) * (Set.Ioc 0 qh).indicator 1 q
            + rhoQ q * (Set.Ioc qh (Real.exp (-Real.exp (-1)))).indicator 1 q
            + Real.exp 1 * q * Real.log q⁻¹ * (Set.Ioo (Real.exp (-Real.exp (-1))) 1).indicator 1 q ∧
        0 ≤ w * (betaQ q (Real.exp 1 / q) * (Set.Ioc 0 qh).indicator 1 q
            + betaQ q (1 / Real.log q⁻¹) * (Set.Ioc qh (Real.exp (-Real.exp (-1)))).indicator 1 q
            + (Set.Ioo (Real.exp (-Real.exp (-1))) 1).indicator 1 q) ∧
        sInf (ratio (Measure.dirac
            (w * (betaQ q (Real.exp 1 / q) * (Set.Ioc 0 qh).indicator 1 q
              + betaQ q (1 / Real.log q⁻¹) * (Set.Ioc qh (Real.exp (-Real.exp (-1)))).indicator 1 q
              + (Set.Ioo (Real.exp (-Real.exp (-1))) 1).indicator 1 q))) '' FClass 1 w q) =
          maximin Pd (FClass 1 w q) := by
  have hα : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨_, hqhf, hp13, hp12⟩ := lemma_D_2.2
  obtain ⟨hqhnum, hqhmem, hiff⟩ := hqhf qh hqh heq
  rw [qLow1, GV1] at hqhmem hiff hp13
  rw [qLow1] at *
  set G := Real.exp (-Real.exp (-1)) with hG
  have hqhG : qh < G := lt_of_le_of_lt hqhnum.2 exp_neg_exp_gt
  have hD1 := proposition_D_1 1 hα w hw q hq
  rw [qLow1] at hD1
  have d1 := lemma_D_1 1 hα q hq
  rw [qLow1, GV1] at d1
  have hanti := (d1.2.2.2 (Or.inr rfl)).1
  have hf2 : ∀ p : ℝ, p ≤ 1 → R2 p = p := fun p hp => R2_eq p hp
  have hL := L_pos q hq
  set L := Real.log q⁻¹ with hLdef
  set B12 := betaQ q (Real.exp 1 / q) with hB12
  set B13 := betaQ q (1 / L) with hB13
  obtain ⟨hB12r, hB12_1⟩ := beta_eq_facts q hq
  rw [← hB12] at hB12r hB12_1
  have hrpos := rLow_pos 1 q hα hq
  have hB12pos : 0 < B12 := lt_of_lt_of_le hrpos hB12r
  have hcross12 : R1 1 q B12 = B12 := by
    have a1 := (hp12 q hq).2.1 B12 ⟨hB12r, le_rfl⟩
    have a2 := (hp12 q hq).2.2 B12 ⟨le_rfl, hB12_1.le⟩
    rw [hf2 B12 hB12_1.le] at a1 a2
    linarith
  rcases le_or_gt q qh with hA | hBC
  · -- low regime: value and price `β_q(e/q)`
    have key : maximin Pd (FClass 1 w q) = B12 ∧
        ∀ r' ∈ rSet 1 1 q, B12 ≤ B12 * Fbar 1 1 q r' B12 / optFun (Fbar 1 1 q r') := by
      rcases lt_or_ge q (Real.exp (-1)) with hlo | hhi
      · obtain ⟨LG, Lv⟩ := low2 (R1 1 q) R2 (rLow 1 1 q) B12 hrpos.le hB12r hB12_1 hf2 hcross12
          hanti
        refine ⟨by rw [hD1.2 hlo, LG.csSup_eq], fun r' hr' => ?_⟩
        have := (lowbound 1 q B12 hα hq ⟨hB12r, hB12_1⟩ r' hr').2 (by rw [qLow1]; exact hlo)
        rwa [Lv] at this
      · have hmemI : q ∈ Set.Icc (Real.exp (-1)) G ∩ Set.Ioo 0 1 :=
          ⟨⟨hhi, by linarith⟩, hq⟩
        have h1312 : B13 ≤ B12 := ((hiff q hmemI).2).mpr hA
        have hq13 := hp13 q ⟨⟨hhi, by linarith⟩, hq⟩
        obtain ⟨LG, Lv⟩ := low3 (R1 1 q) R2 (R3 1 q) (rLow 1 1 q) B12 B13 hrpos.le hB12r hB12_1
          h1312 hf2 hcross12 hanti hq13.2.2.2
        refine ⟨by rw [hD1.1 hhi, LG.csSup_eq], fun r' hr' => ?_⟩
        have := (lowbound 1 q B12 hα hq ⟨hB12r, hB12_1⟩ r' hr').1 (by rw [qLow1]; exact hhi)
        rwa [Lv] at this
    have hi1 : (Set.Ioc (0 : ℝ) qh).indicator (1 : ℝ → ℝ) q = 1 := by
      rw [Set.indicator_of_mem (show q ∈ Set.Ioc (0 : ℝ) qh from ⟨hq.1, hA⟩)]; rfl
    have hi2 : (Set.Ioc qh G).indicator (1 : ℝ → ℝ) q = 0 :=
      Set.indicator_of_notMem (fun h => by linarith [h.1]) _
    have hi3 : (Set.Ioo G 1).indicator (1 : ℝ → ℝ) q = 0 :=
      Set.indicator_of_notMem (fun h => by linarith [h.1]) _
    rw [hi1, hi2, hi3]
    simp only [mul_one, mul_zero, add_zero]
    refine ⟨key.1, by positivity, ?_⟩
    exact pack 1 w q B12 B12 hα hw hq key.1 hB12pos hB12pos.le key.2
  · have hqL : Real.exp (-1) ≤ q := by linarith [hqhmem.1]
    have hL1 := L_le_one q hq hqL
    have hR3eq : Set.EqOn (R3e L) (R3 1 q) (Set.Icc 0 1) :=
      fun p hp => (R3_1 q p hq hqL hp).symm
    have hmono : MonotoneOn (R3 1 q) (Set.Icc 0 1) := (R3e_mono L hL hL1).congr hR3eq
    rcases lt_or_ge q G with hB | hC
    · -- intermediate regime
      have hq13 := hp13 q ⟨⟨hqL, hB⟩, hq⟩
      rw [← hLdef, ← hB13] at hq13
      obtain ⟨_, hB13r, hc31, hc13⟩ := hq13
      have hmemI : q ∈ Set.Icc (Real.exp (-1)) G ∩ Set.Ioo 0 1 := ⟨⟨hqL, hB.le⟩, hq⟩
      have h1213 : B12 ≤ B13 := by
        have := mt ((hiff q hmemI).2).mp (by linarith)
        exact le_of_lt (not_le.mp this)
      -- `β_q(1/log q⁻¹) < 1` since `W(1/L) ≠ 1`
      have hB13_1 : B13 < 1 := by
        obtain ⟨hy0, hye⟩ := W_spec (1 / L) (by positivity)
        set y := lambertW (1 / L) with hy
        have hLe : Real.exp (-1) < L := by
          rw [hLdef, Real.log_inv]
          have := Real.log_lt_log hq.1 hB
          rw [hG, Real.log_exp] at this; linarith
        have hy1 : y < 1 := by
          by_contra hcon; push Not at hcon
          have h1 : 1 * Real.exp 1 ≤ y * Real.exp y :=
            mul_le_mul hcon (Real.exp_le_exp.mpr hcon) (Real.exp_pos _).le hy0
          rw [hye, one_mul, le_div_iff₀ hL] at h1
          have : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
          nlinarith [Real.exp_pos 1]
        have hypos : 0 < y := by
          rcases eq_or_lt_of_le hy0 with h | h
          · rw [← h] at hye; simp at hye; exact absurd hye.symm (by positivity)
          · exact h
        have e : y + 1 / y - 2 = (y - 1) ^ 2 / y := by field_simp; ring
        have : 0 < (y + 1 / y - 2) / L := by
          rw [e]; exact div_pos (div_pos (by nlinarith) hypos) hL
        rw [hB13]; unfold betaQ; rw [← hy, ← hLdef]; linarith
      have hcross : R1 1 q B13 = R3 1 q B13 := by
        have a1 := hc31 B13 ⟨hB13r.1, le_rfl⟩
        have a2 := hc13 B13 ⟨le_rfl, hB13_1⟩
        linarith
      have hf21 : R1 1 q B13 ≤ R2 B13 := (hp12 q hq).2.2 B13 ⟨h1213, hB13_1.le⟩
      obtain ⟨LG, Lv⟩ := mid3 (R1 1 q) R2 (R3 1 q) (rLow 1 1 q) B12 B13 hrpos.le hB13r.1 hB13_1
        hmono hanti hcross hf21
      have hB13pos : 0 < B13 := lt_of_lt_of_le hrpos hB13r.1
      have hV : R3 1 q B13 = rhoQ q := by
        rw [R3_1 q B13 hq hqL ⟨hB13pos.le, hB13_1.le⟩]
        unfold R3e rhoQ; rw [← hLdef, ← hB13]; ring_nf
      have hval : maximin Pd (FClass 1 w q) = rhoQ q := by
        rw [hD1.1 hqL, LG.csSup_eq, hV]
      have hVpos : 0 < rhoQ q := by
        rw [← hV, R3_1 q B13 hq hqL ⟨hB13pos.le, hB13_1.le⟩]; unfold R3e; positivity
      have hi1 : (Set.Ioc (0 : ℝ) qh).indicator (1 : ℝ → ℝ) q = 0 :=
        Set.indicator_of_notMem (fun h => by linarith [h.2]) _
      have hi2 : (Set.Ioc qh G).indicator (1 : ℝ → ℝ) q = 1 := by
        rw [Set.indicator_of_mem (show q ∈ Set.Ioc qh G from ⟨hBC, hB.le⟩)]; rfl
      have hi3 : (Set.Ioo G 1).indicator (1 : ℝ → ℝ) q = 0 :=
        Set.indicator_of_notMem (fun h => by linarith [h.1]) _
      rw [hi1, hi2, hi3]
      simp only [mul_one, mul_zero, add_zero, zero_add]
      refine ⟨hval, by positivity, ?_⟩
      refine pack 1 w q _ B13 hα hw hq hval hVpos hB13pos.le ?_
      intro r' hr'
      have := (lowbound 1 q B13 hα hq ⟨hB13r.1, hB13_1⟩ r' hr').1 (by rw [qLow1]; exact hqL)
      rwa [Lv, hV] at this
    · -- high regime
      have hLe : L ≤ Real.exp (-1) := by
        rw [hLdef, Real.log_inv]
        have := Real.log_le_log (Real.exp_pos _) hC
        rw [Real.log_exp] at this; linarith
      have heL : Real.exp 1 * L ≤ 1 := by
        have : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos 1]
      have hR31 : R3 1 q 1 = Real.exp 1 * q * L := by
        rw [R3_1 q 1 hq hqL ⟨zero_le_one, le_rfl⟩]; unfold R3e
        rw [mul_one, mul_one, hLdef, exp_L q hq.1]; ring
      have hf13 : ∀ p ∈ Set.Ico (rLow 1 1 q) 1, R3 1 q p ≤ R1 1 q p := fun p hp =>
        d1.1.2 ⟨hC, hq.2.le⟩ p ⟨hp.1, hp.2.le⟩
      have hcont : ContinuousWithinAt (R3 1 q) (Set.Icc 0 1) 1 :=
        (R3e_cont L).continuousWithinAt.congr (fun p hp => (R3_1 q p hq hqL hp))
          (R3_1 q 1 hq hqL ⟨zero_le_one, le_rfl⟩)
      have hVle : Real.exp 1 * q * L ≤ q := by nlinarith [hq.1]
      have hLUB := high3 (R1 1 q) R2 (R3 1 q) (rLow 1 1 q) hrpos.le (rLow_pos_lt1 1 q hα hq)
        hmono hcont hf2 hf13 (by rw [hR31]; linarith [hq.2])
      have hne : ((fun p => min (R1 1 q p) (min (R2 p) (R3 1 q p))) '' Set.Ico 0 1).Nonempty :=
        ⟨_, 0, ⟨le_rfl, zero_lt_one⟩, rfl⟩
      have hval : maximin Pd (FClass 1 w q) = Real.exp 1 * q * L := by
        rw [hD1.1 hqL, hLUB.csSup_eq hne, hR31]
      have hlow : ∀ r' ∈ rSet 1 1 q,
          Real.exp 1 * q * L ≤ 1 * Fbar 1 1 q r' 1 / optFun (Fbar 1 1 q r') := by
        intro r' hr'
        have := lowbound_one 1 q hα hq (by rw [qLow1]; exact hqL) r' hr'
        rw [hR31, min_eq_right hVle] at this
        exact this
      have hfin := pack 1 w q _ 1 hα hw hq hval (mul_pos (mul_pos (Real.exp_pos 1) hq.1) hL) zero_le_one hlow
      have hi1 : (Set.Ioc (0 : ℝ) qh).indicator (1 : ℝ → ℝ) q = 0 :=
        Set.indicator_of_notMem (fun h => by linarith [h.2]) _
      rw [hi1]
      rcases eq_or_lt_of_le hC with hE | hD
      · -- q = e^{-e^{-1}}: the intermediate formulas coincide with the high ones
        have hi2 : (Set.Ioc qh G).indicator (1 : ℝ → ℝ) q = 1 := by
          rw [Set.indicator_of_mem (show q ∈ Set.Ioc qh G from ⟨hBC, hE.symm.le⟩)]; rfl
        have hi3 : (Set.Ioo G 1).indicator (1 : ℝ → ℝ) q = 0 :=
          Set.indicator_of_notMem (fun h => by linarith [h.1]) _
        rw [hi2, hi3]
        have hLv : L = Real.exp (-1) := by
          rw [hLdef, Real.log_inv, ← hE, hG, Real.log_exp, neg_neg]
        have hinv : 1 / L = Real.exp 1 := by rw [hLv, Real.exp_neg]; simp
        have hB13v : B13 = 1 := by
          rw [hB13]; unfold betaQ; rw [hinv, W_e]; norm_num
        have hrho : rhoQ q = Real.exp 1 * q * L := by
          have hexpL : Real.exp (-L) = q := by rw [hLdef]; exact exp_L q hq.1
          unfold rhoQ; rw [← hLdef, ← hB13, hB13v, mul_one, hexpL]; ring
        rw [hB13v, hrho]
        simp only [mul_one, mul_zero, add_zero, zero_add]
        exact ⟨hval, hw.le, by simpa using hfin⟩
      · have hi2 : (Set.Ioc qh G).indicator (1 : ℝ → ℝ) q = 0 :=
          Set.indicator_of_notMem (fun h => by linarith [h.2]) _
        have hi3 : (Set.Ioo G 1).indicator (1 : ℝ → ℝ) q = 1 := by
          rw [Set.indicator_of_mem (show q ∈ Set.Ioo G 1 from ⟨hD, hq.2⟩)]; rfl
        rw [hi2, hi3]
        simp only [mul_one, mul_zero, add_zero, zero_add]
        exact ⟨hval, hw.le, by simpa using hfin⟩

end SPPT2

open SinglePointPricing.Det MeasureTheory in
theorem solution :
    (∀ w q : ℝ, 0 < w → q ∈ Set.Ioo (0 : ℝ) 1 →
      maximin Pd (FClass 0 w q) =
          2 * Real.sqrt q / (1 + Real.sqrt q) * (Set.Ioc (0 : ℝ) (1 / 4)).indicator 1 q
          + (3 - 4 * q) / (4 * (1 - q)) * (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator 1 q
          + (1 - q) * (Set.Ioo (1 / 2 : ℝ) 1).indicator 1 q ∧
      0 ≤ w * (2 * Real.sqrt q / (1 + Real.sqrt q) * (Set.Ioc (0 : ℝ) (1 / 4)).indicator 1 q
          + q * (3 - 4 * q) / (1 - q) * (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator 1 q
          + (Set.Ioo (1 / 2 : ℝ) 1).indicator 1 q) ∧
      sInf (ratio (Measure.dirac
          (w * (2 * Real.sqrt q / (1 + Real.sqrt q) * (Set.Ioc (0 : ℝ) (1 / 4)).indicator 1 q
            + q * (3 - 4 * q) / (1 - q) * (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator 1 q
            + (Set.Ioo (1 / 2 : ℝ) 1).indicator 1 q))) '' FClass 0 w q) =
        maximin Pd (FClass 0 w q)) ∧
    (∃! qh : ℝ, qh ∈ Set.Icc 0 1 ∧
      lambertW (1 / Real.log qh⁻¹) * lambertW (Real.exp 1 / qh) = 1) ∧
    (∀ qh : ℝ, qh ∈ Set.Icc 0 1 →
      lambertW (1 / Real.log qh⁻¹) * lambertW (Real.exp 1 / qh) = 1 →
      qh ∈ Set.Icc (0.52 : ℝ) 0.53 ∧
      ∀ w q : ℝ, 0 < w → q ∈ Set.Ioo (0 : ℝ) 1 →
        maximin Pd (FClass 1 w q) =
            betaQ q (Real.exp 1 / q) * (Set.Ioc 0 qh).indicator 1 q
            + rhoQ q * (Set.Ioc qh (Real.exp (-Real.exp (-1)))).indicator 1 q
            + Real.exp 1 * q * Real.log q⁻¹ * (Set.Ioo (Real.exp (-Real.exp (-1))) 1).indicator 1 q ∧
        0 ≤ w * (betaQ q (Real.exp 1 / q) * (Set.Ioc 0 qh).indicator 1 q
            + betaQ q (1 / Real.log q⁻¹) * (Set.Ioc qh (Real.exp (-Real.exp (-1)))).indicator 1 q
            + (Set.Ioo (Real.exp (-Real.exp (-1))) 1).indicator 1 q) ∧
        sInf (ratio (Measure.dirac
            (w * (betaQ q (Real.exp 1 / q) * (Set.Ioc 0 qh).indicator 1 q
              + betaQ q (1 / Real.log q⁻¹) * (Set.Ioc qh (Real.exp (-Real.exp (-1)))).indicator 1 q
              + (Set.Ioo (Real.exp (-Real.exp (-1))) 1).indicator 1 q))) '' FClass 1 w q) =
          maximin Pd (FClass 1 w q)) := by
  refine ⟨fun w q hw hq => SPPT2.regular w q hw hq, lemma_D_2.2.1, fun qh hqh heq => ?_⟩
  exact ⟨(lemma_D_2.2.2.1 qh hqh heq).1, fun w q hw hq => SPPT2.mhr qh hqh heq w q hw hq⟩
