-- Prove2me | solution 1 for SinglePointPricing.Det.proposition_D_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T09:52:14.126625+00:00
-- url     : https://prove2.me/submissions/4a08bfd7-469f-4157-ae10-04cb78c79e53

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase
import Theorems.Thm_SinglePointPricing_Det_theorem_1
import Theorems.Thm_SinglePointPricing_Det_lemma_C_2
import Theorems.Thm_SinglePointPricing_Det_propD1_worst_terms
import Theorems.Thm_SinglePointPricing_Det_eq_4_1

namespace SPPP1
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

lemma rLow_scale (α w q : ℝ) : rLow α w q = w * rLow α 1 q := by
  rw [rLow_eqw, rLow_eqw]; ring

lemma A_scale (α w q x : ℝ) (hw : 0 < w) :
    (fun r => (w * x) * Fbar α w q r (w * x) / r) '' Set.Ico (rLow α w q) (w * x) =
      (fun r => x * Fbar α 1 q r x / r) '' Set.Ico (rLow α 1 q) x := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨r / w, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hw, mul_comm, ← rLow_scale]; exact hr.1
    · rw [div_lt_iff₀ hw, mul_comm]; exact hr.2
    · simp only; rw [Fbar_scale α w q r x hw]; field_simp
  · rintro ⟨r, hr, rfl⟩
    refine ⟨w * r, ⟨?_, ?_⟩, ?_⟩
    · rw [rLow_scale]; exact mul_le_mul_of_nonneg_left hr.1 hw.le
    · exact mul_lt_mul_of_pos_left hr.2 hw
    · simp only; rw [Fbar_scale α w q (w * r) x hw]
      have : w * r / w = r := by field_simp
      rw [this]; field_simp

lemma C_scale (α w q x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (fun r => (w * x) * Fbar α w q r (w * x) / optFun (Fbar α w q r)) ''
        {r | w ≤ r ∧ α * GammaAInv α q * r ≤ w} =
      (fun r => x * Fbar α 1 q r x / optFun (Fbar α 1 q r)) ''
        {r | 1 ≤ r ∧ α * GammaAInv α q * r ≤ 1} := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨r / w, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hw, one_mul]; exact hr.1
    · rw [show α * GammaAInv α q * (r / w) = (α * GammaAInv α q * r) / w by ring,
        div_le_one hw]; exact hr.2
    · simp only
      rw [Fbar_scale α w q r x hw, optFun_scale α w q r hα hw hq (Or.inr hr)]
      rw [mul_assoc, mul_div_mul_left _ _ hw.ne']
  · rintro ⟨r, hr, rfl⟩
    have hr' : w * r ∈ {r | w ≤ r ∧ α * GammaAInv α q * r ≤ w} := by
      refine ⟨by nlinarith [hr.1], ?_⟩
      have := mul_le_mul_of_nonneg_left hr.2 hw.le
      nlinarith
    refine ⟨w * r, hr', ?_⟩
    simp only
    rw [Fbar_scale α w q (w * r) x hw, optFun_scale α w q (w * r) hα hw hq (Or.inr hr')]
    have : w * r / w = r := by field_simp
    rw [this, mul_assoc, mul_div_mul_left _ _ hw.ne']

/-- the normalized inner worst case. -/
noncomputable def Iq (α q x : ℝ) : ℝ :=
  sInf (((fun r => x * Fbar α 1 q r x / r) '' Set.Ico (rLow α 1 q) x) ∪ {x} ∪
    ((fun r => x * Fbar α 1 q r x / optFun (Fbar α 1 q r)) ''
      {r | 1 ≤ r ∧ α * GammaAInv α q * r ≤ 1}))

lemma image_eq (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (fun p : ℝ =>
        sInf (((fun r => p * Fbar α w q r p / r) '' Set.Ico (rLow α w q) p) ∪ {p / w} ∪
          ((fun r => p * Fbar α w q r p / optFun (Fbar α w q r)) ''
            {r | w ≤ r ∧ α * GammaAInv α q * r ≤ w}))) '' Set.Icc 0 w =
      (Iq α q) '' Set.Icc 0 1 := by
  have key : ∀ x : ℝ,
      sInf (((fun r => (w * x) * Fbar α w q r (w * x) / r) '' Set.Ico (rLow α w q) (w * x)) ∪
        {w * x / w} ∪ ((fun r => (w * x) * Fbar α w q r (w * x) / optFun (Fbar α w q r)) ''
            {r | w ≤ r ∧ α * GammaAInv α q * r ≤ w})) = Iq α q x := by
    intro x
    rw [A_scale α w q x hw, C_scale α w q x hα hw hq]
    have : w * x / w = x := by field_simp
    rw [this]; rfl
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x, p = w * x := ⟨p / w, by field_simp⟩
    refine ⟨x, ⟨?_, ?_⟩, (key x).symm⟩
    · nlinarith [hp.1]
    · nlinarith [hp.2]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨w * x, ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩, key x⟩

lemma A_empty (α q x : ℝ) (hx : x ≤ rLow α 1 q) :
    (fun r => x * Fbar α 1 q r x / r) '' Set.Ico (rLow α 1 q) x = ∅ := by
  rw [Set.Ico_eq_empty (not_lt.mpr hx), Set.image_empty]

lemma C_empty (α q x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hqL : q < qLow α) :
    (fun r => x * Fbar α 1 q r x / optFun (Fbar α 1 q r)) ''
      {r | 1 ≤ r ∧ α * GammaAInv α q * r ≤ 1} = ∅ := by
  rw [Set.image_eq_empty]
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  exact no_high α q r hα hq hqL h1 h2

lemma A_one (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    IsGLB ((fun r => 1 * Fbar α 1 q r 1 / r) '' Set.Ico (rLow α 1 q) 1) q := by
  have e : (fun r => 1 * Fbar α 1 q r 1 / r) '' Set.Ico (rLow α 1 q) 1 =
      (fun r : ℝ => q / r) '' Set.Ico (rLow α 1 q) 1 := by
    apply Set.image_congr
    intro r hr
    rw [Fbar_lt α q r 1 hr.2 hr.2.le le_rfl]
    have : GammaAInv α q * (1 - r) / (1 - r) = GammaAInv α q := by
      have : 1 - r ≠ 0 := by linarith [hr.2]
      field_simp
    rw [this, GA_GAInv α q hα hq.1, one_mul]
  rw [e]
  have := isGLB_div_image_Ico (rLow α 1 q) 1 q (rLow_pos α q hα hq) (rLow_pos_lt1 α q hα hq)
    hq.1.le
  rwa [div_one] at this

lemma glb3 (A C : Set ℝ) (x a c : ℝ) (hA : IsGLB A a) (hC : IsGLB C c) :
    sInf (A ∪ {x} ∪ C) = min a (min x c) := by
  have h := (hA.union (isGLB_singleton (a := x))).union hC
  rw [h.csInf_eq ⟨x, Or.inl (Or.inr rfl)⟩]
  simp [min_assoc]

lemma glb2A (A : Set ℝ) (x a : ℝ) (hA : IsGLB A a) :
    sInf (A ∪ {x} ∪ ∅) = min a x := by
  rw [Set.union_empty]
  have h := hA.union (isGLB_singleton (a := x))
  rw [h.csInf_eq ⟨x, Or.inr rfl⟩]

lemma glb2C (C : Set ℝ) (x c : ℝ) (hC : IsGLB C c) :
    sInf (∅ ∪ {x} ∪ C) = min x c := by
  rw [Set.empty_union]
  have h := (isGLB_singleton (a := x)).union hC
  rw [h.csInf_eq ⟨x, Or.inl rfl⟩]

lemma glb1 (x : ℝ) : sInf (∅ ∪ {x} ∪ (∅ : Set ℝ)) = x := by simp

/-- the two suprema agree. -/
lemma sup_equal (I M : ℝ → ℝ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hmid : ∀ x ∈ Set.Ioo a 1, I x = M x)
    (hlowI : ∀ x ∈ Set.Icc 0 a, I x ≤ I a)
    (hlowM : ∀ x ∈ Set.Icc 0 a, M x ≤ I x)
    (haM : I a = M a)
    (hMle1 : ∀ x ∈ Set.Ico 0 1, M x ≤ 1)
    (h1 : ∀ ε > 0, ∃ x ∈ Set.Ico 0 1, I 1 - ε < M x) :
    sSup (I '' Set.Icc 0 1) = sSup (M '' Set.Ico 0 1) := by
  have hne : (M '' Set.Ico 0 1).Nonempty := ⟨M 0, 0, ⟨le_rfl, zero_lt_one⟩, rfl⟩
  have hbdd : BddAbove (M '' Set.Ico 0 1) := ⟨1, by rintro _ ⟨x, hx, rfl⟩; exact hMle1 x hx⟩
  have hM : ∀ x ∈ Set.Ico 0 1, M x ≤ sSup (M '' Set.Ico 0 1) :=
    fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  refine IsLUB.csSup_eq ?_ ⟨I 0, Set.mem_image_of_mem _ (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)⟩
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    by_cases hxa : x ≤ a
    · exact le_trans (hlowI x ⟨hx.1, hxa⟩) (haM ▸ hM a ⟨ha0, ha1⟩)
    · push Not at hxa
      rcases eq_or_lt_of_le hx.2 with h | h
      · rw [h]
        by_contra hcon; push Not at hcon
        obtain ⟨y, hy, hlt⟩ := h1 (I 1 - sSup (M '' Set.Ico 0 1)) (by linarith)
        linarith [hM y hy]
      · rw [hmid x ⟨hxa, h⟩]; exact hM x ⟨by linarith, h⟩
  · intro b hb
    apply csSup_le hne
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxa : x ≤ a
    · exact le_trans (hlowM x ⟨hx.1, hxa⟩) (hb ⟨x, ⟨hx.1, hx.2.le⟩, rfl⟩)
    · push Not at hxa
      rw [← hmid x ⟨hxa, hx.2⟩]; exact hb ⟨x, ⟨hx.1, hx.2.le⟩, rfl⟩

lemma approach (g M : ℝ → ℝ) (a : ℝ) (ha1 : a < 1)
    (hg : ContinuousWithinAt g (Set.Icc 0 1) 1) (ha0 : 0 ≤ a)
    (hgM : ∀ x ∈ Set.Ioo a 1, g x ≤ M x) :
    ∀ ε > 0, ∃ x ∈ Set.Ico 0 1, g 1 - ε < M x := by
  intro ε hε
  rw [Metric.continuousWithinAt_iff] at hg
  obtain ⟨δ, hδ, hball⟩ := hg ε hε
  set m := max a (1 - δ / 2) with hm
  have hm1 : m < 1 := max_lt ha1 (by linarith)
  set p := (m + 1) / 2 with hp
  have hpm : m < p := by rw [hp]; linarith
  have hp1 : p < 1 := by rw [hp]; linarith
  have hap : a < p := lt_of_le_of_lt (le_max_left _ _) hpm
  have hδp : 1 - δ / 2 < p := lt_of_le_of_lt (le_max_right _ _) hpm
  have hdist : dist p 1 < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have h3 := hball ⟨by linarith, hp1.le⟩ hdist
  rw [Real.dist_eq, abs_lt] at h3
  exact ⟨p, ⟨by linarith, hp1⟩, by linarith [hgM p ⟨hap, hp1⟩, h3.1]⟩

theorem main (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) (hw : 0 < w) (q : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (qLow α ≤ q → maximin Pd (FClass α w q) =
      sSup ((fun p : ℝ => min (R1 α q p) (min (R2 p) (R3 α q p))) '' Set.Ico 0 1)) ∧
    (q < qLow α → maximin Pd (FClass α w q) =
      sSup ((fun p : ℝ => min (R1 α q p) (R2 p)) '' Set.Ico 0 1)) := by
  have D := propD1_worst_terms α hα q hq
  have h41 := eq_4_1 α w q hα hw hq
  rw [image_eq α w q hα hw hq] at h41
  rw [h41]
  have hL := rLow_pos α q hα hq
  have hL1 := rLow_pos_lt1 α q hα hq
  set a := rLow α 1 q with ha
  have hR1a := R1_at_rLow α q hα hq
  rw [← ha] at hR1a
  constructor
  · intro hqL
    have hC : ∀ x ∈ Set.Icc (0 : ℝ) 1, IsGLB ((fun r => x * Fbar α 1 q r x / optFun (Fbar α 1 q r)) ''
        {r | 1 ≤ r ∧ α * GammaAInv α q * r ≤ 1}) (R3 α q x) := fun x hx => D.2 hqL x hx
    have hmono := R3_mono α q hα hq hqL
    have hIlow : ∀ x ∈ Set.Icc 0 a, Iq α q x = min x (R3 α q x) := by
      intro x hx
      unfold Iq; rw [A_empty α q x hx.2]
      exact glb2C _ x _ (hC x ⟨hx.1, le_trans hx.2 hL1.le⟩)
    apply sup_equal (Iq α q) _ a hL.le hL1
    · intro x hx
      unfold Iq
      rw [glb3 _ _ x _ _ (D.1 x hx).isGLB (hC x ⟨by linarith [hx.1], hx.2.le⟩),
        R2_eq x hx.2.le]
    · intro x hx
      rw [hIlow x hx, hIlow a ⟨hL.le, le_rfl⟩]
      exact min_le_min hx.2 (hmono ⟨hx.1, le_trans hx.2 hL1.le⟩ ⟨hL.le, hL1.le⟩ hx.2)
    · intro x hx
      rw [hIlow x hx, R2_eq x (le_trans hx.2 hL1.le)]
      exact min_le_right _ _
    · rw [hIlow a ⟨hL.le, le_rfl⟩, hR1a, R2_eq a hL1.le]
      exact (min_eq_right (le_trans (min_le_left _ _) hL1.le)).symm
    · intro x hx
      exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (by rw [R2_eq x hx.2.le]; exact hx.2.le))
    · have hI1 : Iq α q 1 = min q (min 1 (R3 α q 1)) := by
        unfold Iq
        exact glb3 _ _ 1 _ _ (A_one α q hα hq) (hC 1 ⟨zero_le_one, le_rfl⟩)
      have := approach (fun x => min (x * q) (min x (R3 α q x)))
        (fun p : ℝ => min (R1 α q p) (min (R2 p) (R3 α q p))) a hL1
        (by
          exact ContinuousWithinAt.inf (by fun_prop)
            (ContinuousWithinAt.inf continuousWithinAt_id (R3_cont α q hα hq hqL)))
        hL.le (by
          intro x hx
          rw [R2_eq x hx.2.le]
          exact min_le_min (R1_ge α q x hα hq hx) le_rfl)
      simpa [hI1] using this
  · intro hqL
    have hIlow : ∀ x ∈ Set.Icc 0 a, Iq α q x = x := by
      intro x hx
      unfold Iq; rw [A_empty α q x hx.2, C_empty α q x hα hq hqL]
      exact glb1 x
    apply sup_equal (Iq α q) _ a hL.le hL1
    · intro x hx
      unfold Iq
      rw [C_empty α q x hα hq hqL, glb2A _ x _ (D.1 x hx).isGLB, R2_eq x hx.2.le]
    · intro x hx
      rw [hIlow x hx, hIlow a ⟨hL.le, le_rfl⟩]; exact hx.2
    · intro x hx
      rw [hIlow x hx, R2_eq x (le_trans hx.2 hL1.le)]
      exact min_le_right _ _
    · rw [hIlow a ⟨hL.le, le_rfl⟩, hR1a, R2_eq a hL1.le, min_eq_right hL1.le]
    · intro x hx
      exact le_trans (min_le_right _ _) (by rw [R2_eq x hx.2.le]; exact hx.2.le)
    · have hI1 : Iq α q 1 = min q 1 := by
        unfold Iq
        rw [C_empty α q 1 hα hq hqL]
        exact glb2A _ 1 _ (A_one α q hα hq)
      have := approach (fun x => min (x * q) x)
        (fun p : ℝ => min (R1 α q p) (R2 p)) a hL1
        (ContinuousWithinAt.inf (by fun_prop) continuousWithinAt_id)
        hL.le (by
          intro x hx
          rw [R2_eq x hx.2.le]
          exact min_le_min (R1_ge α q x hα hq hx) le_rfl)
      simpa [hI1] using this

end SPPP1

open SinglePointPricing.Det in
theorem solution (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) (hw : 0 < w) (q : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (qLow α ≤ q → maximin Pd (FClass α w q) =
      sSup ((fun p : ℝ => min (R1 α q p) (min (R2 p) (R3 α q p))) '' Set.Ico 0 1)) ∧
    (q < qLow α → maximin Pd (FClass α w q) =
      sSup ((fun p : ℝ => min (R1 α q p) (R2 p)) '' Set.Ico 0 1)) :=
  SPPP1.main α hα w hw q hq
