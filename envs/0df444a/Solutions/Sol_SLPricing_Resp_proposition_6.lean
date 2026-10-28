-- Prove2me | solution 1 for SLPricing.Resp.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:09:44.929599+00:00
-- url     : https://prove2.me/submissions/bd17bb01-2dc4-4276-b7d4-1ffab05a72c1

import Mathlib
import Definitions.Def_SLPricing_Resp_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

set_option autoImplicit false

namespace SLPricing.Resp.P6

open SLPricing.Resp

/-! ## Part 1: the benchmark without social learning -/

lemma second_le (c β p : ℝ) (hc : 0 ≤ c) (R : Set ℝ) (hR : R ⊆ Icc 0 β) :
    (p - c) * (volume {x | x ∈ R ∧ p ≤ x}).toReal ≤ (max (β - c) 0) ^ 2 / 4 := by
  have hnn : 0 ≤ (volume {x | x ∈ R ∧ p ≤ x}).toReal := ENNReal.toReal_nonneg
  rcases le_or_gt p c with hpc | hpc
  · have : (p - c) * (volume {x | x ∈ R ∧ p ≤ x}).toReal ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hnn
    exact this.trans (by positivity)
  · have hsub : {x | x ∈ R ∧ p ≤ x} ⊆ Icc p β := fun x hx => ⟨hx.2, (hR hx.1).2⟩
    have hle : (volume {x | x ∈ R ∧ p ≤ x}).toReal ≤ max (β - p) 0 := by
      have := ENNReal.toReal_mono (by simp) (measure_mono (μ := volume) hsub)
      rwa [Real.volume_Icc, ENNReal.toReal_ofReal'] at this
    calc (p - c) * (volume {x | x ∈ R ∧ p ≤ x}).toReal ≤ (p - c) * max (β - p) 0 :=
          mul_le_mul_of_nonneg_left hle (by linarith)
      _ ≤ (max (β - c) 0) ^ 2 / 4 := by
          rcases le_total (β - p) 0 with h | h
          · rw [max_eq_right h, mul_zero]; positivity
          · rw [max_eq_left h, max_eq_left (by linarith)]
            nlinarith [sq_nonneg (β + c - 2 * p)]

lemma poly_bounds (a d t : ℝ) (ha : 0 < a) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (ht0 : 0 ≤ t)
    (hta : t ≤ a) :
    (t - d * t / 2) * (a - t) + t ^ 2 / 4 ≤ a ^ 2 / 3 ∧
    (t - d * t / 2) * (a - t) + t ^ 2 / 4 ≤ a ^ 2 / 4 + (1 - d) * a ^ 2 / 8 := by
  constructor
  · nlinarith [sq_nonneg (t - 2 * a / 3), mul_nonneg hd0 (mul_nonneg ht0 (sub_nonneg.2 hta))]
  · nlinarith [sq_nonneg (a - t), mul_nonneg (sub_nonneg.2 hd1) (sq_nonneg (a - 2 * t))]

set_option maxHeartbeats 1000000 in
lemma noSL_core (c d p₁ p₂ : ℝ) (B : Set ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) (hBm : MeasurableSet B) (hBsub : B ⊆ Icc 0 1)
    (hopt : ∀ p, (p - c) * (volume {x | x ∈ Icc (0:ℝ) 1 \ B ∧ p ≤ x}).toReal ≤
        (p₂ - c) * (volume {x | x ∈ Icc (0:ℝ) 1 \ B ∧ p₂ ≤ x}).toReal)
    (hBuy : ∀ x ∈ B, 0 ≤ x - p₁ ∧ d * max (x - p₂) 0 ≤ x - p₁)
    (hDel : ∀ x ∈ Icc (0:ℝ) 1 \ B, x - p₁ ≤ d * max (x - p₂) 0) :
    (p₁ - c) * (volume B).toReal +
        (p₂ - c) * (volume {x | x ∈ Icc (0:ℝ) 1 \ B ∧ p₂ ≤ x}).toReal ≤ (1 - c) ^ 2 / 3 ∧
    (p₁ - c) * (volume B).toReal +
        (p₂ - c) * (volume {x | x ∈ Icc (0:ℝ) 1 \ B ∧ p₂ ≤ x}).toReal ≤
      (1 - c) ^ 2 / 4 + (1 - d) * (1 - c) ^ 2 / 8 := by
  classical
  set R := Icc (0:ℝ) 1 \ B with hRdef
  set L₂ := (volume {x | x ∈ R ∧ p₂ ≤ x}).toReal with hL₂
  have ha0 : 0 < 1 - c := by linarith
  have hfin : ∀ S ⊆ Icc (0:ℝ) 1, volume S ≠ ∞ := fun S hS =>
    ne_top_of_le_ne_top (by simp) (measure_mono (μ := volume) hS)
  -- reduce to: profit ≤ (1-c)^2/4, or the polynomial bound
  suffices H : (p₁ - c) * (volume B).toReal + (p₂ - c) * L₂ ≤ (1 - c) ^ 2 / 4 ∨
      ∃ t, 0 ≤ t ∧ t ≤ 1 - c ∧ (p₁ - c) * (volume B).toReal + (p₂ - c) * L₂ ≤
        (t - d * t / 2) * ((1 - c) - t) + t ^ 2 / 4 by
    rcases H with H | ⟨t, ht0, hta, H⟩
    · constructor
      · nlinarith
      · nlinarith [mul_nonneg (sub_nonneg.2 hd1) (sq_nonneg (1 - c))]
    · obtain ⟨h1, h2⟩ := poly_bounds (1 - c) d t ha0 hd0 hd1 ht0 hta
      exact ⟨H.trans h1, H.trans h2⟩
  by_cases hT : d = 1 ∧ p₁ = p₂
  · -- tie case: one price, everybody who buys pays p₁
    left
    obtain ⟨-, hp⟩ := hT
    subst hp
    set S := {x | x ∈ R ∧ p₁ ≤ x} with hS
    have hdisj : Disjoint S B := by
      rw [Set.disjoint_left]; intro x hx hxB; exact hx.1.2 hxB
    have hU : volume (S ∪ B) = volume S + volume B := measure_union hdisj hBm
    have hsubU : S ∪ B ⊆ Icc 0 1 := by
      rintro x (hx | hx)
      · exact hx.1.1
      · exact hBsub hx
    have heq : {x | x ∈ S ∪ B ∧ p₁ ≤ x} = S ∪ B := by
      ext x; constructor
      · exact fun h => h.1
      · intro h; refine ⟨h, ?_⟩
        rcases h with h | h
        · exact h.2
        · linarith [(hBuy x h).1]
    have h2 := second_le c 1 p₁ hc0 (S ∪ B) hsubU
    rw [heq, hU, ENNReal.toReal_add (hfin S (fun x hx => hx.1.1)) (hfin B hBsub),
      max_eq_left (by linarith)] at h2
    nlinarith
  -- ordering of early and late buyers
  have hord : ∀ x ∈ R, ∀ y ∈ B, x ≤ y := by
    intro x hx y hy
    by_contra hlt
    push Not at hlt
    have h1 := hDel x hx
    obtain ⟨h2, h3⟩ := hBuy y hy
    apply hT
    rcases le_total (x - p₂) 0 with hx2 | hx2 <;>
      rcases le_total (y - p₂) 0 with hy2 | hy2 <;>
      simp only [max_eq_left, max_eq_right, hx2, hy2] at h1 h3 <;>
      constructor <;> nlinarith
  have hBdd : BddBelow B := ⟨0, fun y hy => (hBsub hy).1⟩
  set β : ℝ := if B.Nonempty then sInf B else 1 with hβdef
  have hβ01 : 0 ≤ β ∧ β ≤ 1 := by
    by_cases hne : B.Nonempty
    · rw [hβdef, if_pos hne]
      obtain ⟨y, hy⟩ := hne
      exact ⟨le_csInf ⟨y, hy⟩ (fun z hz => (hBsub hz).1), (csInf_le hBdd hy).trans (hBsub hy).2⟩
    · rw [hβdef, if_neg hne]; norm_num
  have hBβ : B ⊆ Icc β 1 := by
    intro x hx
    have hne : B.Nonempty := ⟨x, hx⟩
    rw [hβdef, if_pos hne]
    exact ⟨csInf_le hBdd hx, (hBsub hx).2⟩
  have hIoc : Ioc β 1 ⊆ B := by
    intro x hx
    by_contra hxB
    have hxR : x ∈ R := ⟨⟨by linarith [hx.1, hβ01.1], hx.2⟩, hxB⟩
    by_cases hne : B.Nonempty
    · have : x ≤ sInf B := le_csInf hne (fun y hy => hord x hxR y hy)
      rw [hβdef, if_pos hne] at hx
      linarith [hx.1]
    · rw [hβdef, if_neg hne] at hx
      linarith [hx.1, hx.2]
  have hRβ : R ⊆ Icc 0 β := by
    intro x hx
    refine ⟨hx.1.1, ?_⟩
    by_contra h
    push Not at h
    exact hx.2 (hIoc ⟨h, hx.1.2⟩)
  have hIco : Ico 0 β ⊆ R := by
    intro x hx
    refine ⟨⟨hx.1, by linarith [hx.2, hβ01.2]⟩, fun hxB => ?_⟩
    linarith [(hBβ hxB).1, hx.2]
  have hmass : (volume B).toReal = 1 - β := by
    have h1 : volume B = ENNReal.ofReal (1 - β) := by
      apply le_antisymm
      · simpa [Real.volume_Icc] using measure_mono (μ := volume) hBβ
      · simpa [Real.volume_Ioc] using measure_mono (μ := volume) hIoc
    rw [h1, ENNReal.toReal_ofReal (by linarith [hβ01.2])]
  have hV₂ : (p₂ - c) * L₂ ≤ (max (β - c) 0) ^ 2 / 4 := second_le c β p₂ hc0 R hRβ
  have hL₂nn : 0 ≤ L₂ := ENNReal.toReal_nonneg
  rw [hmass]
  by_cases hβ1 : β = 1
  · left
    rw [hβ1] at hV₂ ⊢
    rw [max_eq_left (by linarith)] at hV₂
    nlinarith
  have hβlt : β < 1 := lt_of_le_of_ne hβ01.2 hβ1
  -- price bound from the marginal early buyer
  have hp₁ : p₁ ≤ β - d * max (β - p₂) 0 := by
    by_contra h
    push Not at h
    set ε := p₁ - (β - d * max (β - p₂) 0) with hε
    have hεpos : 0 < ε := by linarith
    set y := min 1 (β + ε / 2) with hy
    have hy1 : y ≤ 1 := min_le_left _ _
    have hy2 : y ≤ β + ε / 2 := min_le_right _ _
    have hyβ : β < y := lt_min hβlt (by linarith)
    have hyB : y ∈ B := hIoc ⟨hyβ, hy1⟩
    have h3 := (hBuy y hyB).2
    have hmono : max (β - p₂) 0 ≤ max (y - p₂) 0 := max_le_max (by linarith) le_rfl
    nlinarith [mul_le_mul_of_nonneg_left hmono hd0]
  by_cases hβc : β ≤ c
  · left
    rw [max_eq_right (by linarith)] at hV₂
    have : 0 ≤ d * max (β - p₂) 0 := mul_nonneg hd0 (le_max_right _ _)
    nlinarith
  push Not at hβc
  right
  refine ⟨β - c, by linarith, by linarith, ?_⟩
  rw [max_eq_left (by linarith)] at hV₂
  -- lower bound for the second-period value from p = (β + c)/2
  have hlow : (β - c) / 2 ≤ (volume {x | x ∈ R ∧ (β + c) / 2 ≤ x}).toReal := by
    have hsub : Ico ((β + c) / 2) β ⊆ {x | x ∈ R ∧ (β + c) / 2 ≤ x} := by
      intro x hx
      exact ⟨hIco ⟨by linarith [hx.1], hx.2⟩, hx.1⟩
    have := ENNReal.toReal_mono (hfin _ (fun x hx => hx.1.1)) (measure_mono (μ := volume) hsub)
    rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)] at this
    linarith
  have hopt' := hopt ((β + c) / 2)
  have hge : (β - c) ^ 2 / 4 ≤ (p₂ - c) * L₂ := by
    have : (β - c) / 2 * ((β - c) / 2) ≤ ((β + c) / 2 - c) *
        (volume {x | x ∈ R ∧ (β + c) / 2 ≤ x}).toReal := by
      rw [show (β + c) / 2 - c = (β - c) / 2 by ring]
      exact mul_le_mul_of_nonneg_left hlow (by linarith)
    nlinarith
  have hLup : L₂ ≤ max (β - p₂) 0 := by
    have hsub : {x | x ∈ R ∧ p₂ ≤ x} ⊆ Icc p₂ β := fun x hx => ⟨hx.2, (hRβ hx.1).2⟩
    have := ENNReal.toReal_mono (by simp) (measure_mono (μ := volume) hsub)
    rwa [Real.volume_Icc, ENNReal.toReal_ofReal'] at this
  have hp2c : c < p₂ := by
    by_contra h
    push Not at h
    have : (p₂ - c) * L₂ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hL₂nn
    nlinarith
  have hmaxpos : (β - c) ^ 2 / 4 ≤ (p₂ - c) * max (β - p₂) 0 :=
    hge.trans (mul_le_mul_of_nonneg_left hLup (by linarith))
  have hβp2 : p₂ < β := by
    by_contra h
    push Not at h
    rw [max_eq_right (by linarith)] at hmaxpos
    nlinarith
  rw [max_eq_left (by linarith)] at hmaxpos
  have hp2eq : β - p₂ = (β - c) / 2 := by
    nlinarith [sq_nonneg (β + c - 2 * p₂)]
  rw [max_eq_left (by linarith), hp2eq] at hp₁
  have h1β : 0 ≤ 1 - β := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hp₁ h1β]

lemma prePost_noSL (Q : Params) (n : ℝ) : prePost Q.noSL n = Measure.dirac 0 := by
  simp [prePost, preVar, Params.noSL, gaussianReal_zero_var]

lemma noSL_value_le (P : Params) (hP : P.Standing) (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    respValue (P.withδc d).noSL ≤ (((1 - P.c) ^ 2 / 3 : ℝ) : EReal) ∧
    respValue (P.withδc d).noSL ≤
      (((1 - P.c) ^ 2 / 4 + (1 - d) * (1 - P.c) ^ 2 / 8 : ℝ) : EReal) := by
  have key : ∀ (p₁ : ℝ) (B : Set ℝ) (s : ℝ → ℝ), IsRespEq (P.withδc d).noSL p₁ B s →
      respProfit (P.withδc d).noSL p₁ B s ≤ (1 - P.c) ^ 2 / 3 ∧
      respProfit (P.withδc d).noSL p₁ B s ≤ (1 - P.c) ^ 2 / 4 + (1 - d) * (1 - P.c) ^ 2 / 8 := by
    rintro p₁ B s ⟨hBm, hBsub, -, hopt, hbuy, hdel⟩
    have hc : (P.withδc d).noSL.c = P.c := rfl
    have hδ : (P.withδc d).noSL.δc = d := rfl
    simp only [BuysEarlyResp, DelaysResp, prePost_noSL, integral_dirac, add_zero, hδ] at hbuy hdel
    simp only [secondProfit, lateMass, add_zero, hc] at hopt
    have := noSL_core P.c d p₁ (s 0) B hP.c_nonneg hP.c_lt_one hd0 hd1 hBm hBsub
      (fun p => by simpa using hopt 0 p) hbuy hdel
    simpa only [respProfit, secondProfit, lateMass, prePost_noSL, integral_dirac, add_zero, hc,
      mass] using this
  constructor
  · exact iSup_le fun o => EReal.coe_le_coe_iff.2 (key _ _ _ o.2).1
  · exact iSup_le fun o => EReal.coe_le_coe_iff.2 (key _ _ _ o.2).2

/-! ## Part 2: social learning, a threshold equilibrium -/

/-- the optimal second-period markup `p₂ - q_u`, clamped to `[0, θ]` -/
noncomputable def uf (c θ q : ℝ) : ℝ := max 0 (min ((θ + c - q) / 2) θ)

lemma uf_cont (c θ : ℝ) : Continuous (uf c θ) := by
  unfold uf; fun_prop

lemma uf_bounds (c θ q : ℝ) (hθ : 0 ≤ θ) : 0 ≤ uf c θ q ∧ uf c θ q ≤ θ :=
  ⟨le_max_left _ _, max_le hθ (min_le_right _ _)⟩

lemma uf_cases (c θ q : ℝ) (hθ : 0 ≤ θ) :
    ((θ + c - q) / 2 ≤ 0 ∧ uf c θ q = 0) ∨ (θ ≤ (θ + c - q) / 2 ∧ uf c θ q = θ) ∨
    (0 ≤ (θ + c - q) / 2 ∧ (θ + c - q) / 2 ≤ θ ∧ uf c θ q = (θ + c - q) / 2) := by
  unfold uf
  rcases le_total ((θ + c - q) / 2) 0 with h | h
  · left; refine ⟨h, ?_⟩; rw [min_eq_left (by linarith), max_eq_left h]
  · rcases le_total θ ((θ + c - q) / 2) with h' | h'
    · right; left; refine ⟨h', ?_⟩; rw [min_eq_right h', max_eq_right hθ]
    · right; right; refine ⟨h, h', ?_⟩; rw [min_eq_left h', max_eq_right h]

lemma lateMass_Icc (θ p q : ℝ) (hθ1 : θ ≤ 1) :
    lateMass (Icc θ 1) p q = max (θ - max 0 (p - q)) 0 := by
  have hset : {x | x ∈ Icc (0:ℝ) 1 \ Icc θ 1 ∧ p ≤ x + q} = Ico (max 0 (p - q)) θ := by
    ext x
    simp only [mem_setOf_eq, mem_diff, mem_Icc, mem_Ico, max_le_iff]
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
      exact ⟨⟨h0, by linarith⟩, lt_of_not_ge (fun h => h2 ⟨h, h1⟩)⟩
    · rintro ⟨⟨h0, h3⟩, h4⟩
      exact ⟨⟨⟨h0, by linarith⟩, fun h => by linarith [h.1]⟩, by linarith⟩
  unfold lateMass
  rw [hset, Real.volume_Ico, ENNReal.toReal_ofReal']

lemma opt_u (c θ q p : ℝ) (hc : 0 ≤ c) (hθ : 0 ≤ θ) :
    (p - c) * max (θ - max 0 (p - q)) 0 ≤
      (q + uf c θ q - c) * max (θ - max 0 (q + uf c θ q - q)) 0 := by
  obtain ⟨hu0, hu1⟩ := uf_bounds c θ q hθ
  have e1 : q + uf c θ q - q = uf c θ q := by ring
  rw [e1, max_eq_right hu0, max_eq_left (show 0 ≤ θ - uf c θ q by linarith)]
  have e2 : q + uf c θ q - c = uf c θ q + q - c := by ring
  rw [e2]
  have key : ∀ z, 0 ≤ z → z ≤ θ →
      (z + q - c) * (θ - z) ≤ (uf c θ q + q - c) * (θ - uf c θ q) := by
    intro z hz0 hzθ
    rcases uf_cases c θ q hθ with ⟨hw, hu⟩ | ⟨hw, hu⟩ | ⟨hw0, hw1, hu⟩ <;> rw [hu]
    · nlinarith [mul_nonneg hz0 (show 0 ≤ q - c - θ by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ θ - z by linarith) (show 0 ≤ -(z + q - c) by linarith)]
    · nlinarith [sq_nonneg (z - (θ + c - q) / 2)]
  rcases le_total (p - q) 0 with h | h
  · rw [max_eq_left h, sub_zero, max_eq_left hθ]
    have := key 0 le_rfl hθ
    nlinarith [mul_nonneg hθ (show 0 ≤ q - p by linarith)]
  · rw [max_eq_right h]
    rcases le_total (θ - (p - q)) 0 with h' | h'
    · rw [max_eq_right h', mul_zero]
      have := key θ hθ le_rfl
      nlinarith
    · rw [max_eq_left h']
      have := key (p - q) h (by linarith)
      have e3 : p - c = p - q + q - c := by ring
      rw [e3]; exact this

/-- the consumers' option value of waiting, for type `x` -/
noncomputable def phi (P : Params) (θ x : ℝ) : ℝ :=
  ∫ q, max (x - uf P.c θ q) 0 ∂(gaussianReal 0 (preVar P (1 - θ)))

/-- the expected second-period profit -/
noncomputable def Gint (P : Params) (θ : ℝ) : ℝ :=
  ∫ q, (uf P.c θ q + q - P.c) * (θ - uf P.c θ q) ∂(gaussianReal 0 (preVar P (1 - θ)))

lemma phi_int (P : Params) (θ x : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun q => max (x - uf P.c θ q) 0) (gaussianReal 0 (preVar P (1 - θ))) := by
  refine Integrable.of_bound
    ((Continuous.max (continuous_const.sub (uf_cont _ _)) continuous_const).aestronglyMeasurable)
    (|x| + θ) (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨h0, h1⟩ := uf_bounds P.c θ q hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [le_abs_self x]) (by positivity)

set_option maxHeartbeats 1000000 in
lemma SL_value_ge (P : Params) (hP : P.Standing) (d θ : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (((θ - d * phi P θ θ - P.c) * (1 - θ) + Gint P θ : ℝ) : EReal) ≤ respValue (P.withδc d) := by
  set s : ℝ → ℝ := fun q => q + uf P.c θ q with hs
  set p₁ := θ - d * phi P θ θ with hp₁
  have hmass : mass (Icc θ 1) = 1 - θ := by
    simp [mass, Real.volume_Icc, ENNReal.toReal_ofReal, sub_nonneg.2 hθ1]
  have hpp : prePost (P.withδc d) (mass (Icc θ 1)) = gaussianReal 0 (preVar P (1 - θ)) := by
    rw [hmass]; rfl
  have hlip : ∀ x y, x ≤ y → phi P θ y ≤ phi P θ x + (y - x) := by
    intro x y hxy
    have hi2 : Integrable (fun q => max (x - uf P.c θ q) 0 + (y - x))
        (gaussianReal 0 (preVar P (1 - θ))) := (phi_int P θ x hθ0).add (integrable_const (y - x))
    have h := integral_mono (phi_int P θ y hθ0) hi2
      (fun q => show max (y - uf P.c θ q) 0 ≤ max (x - uf P.c θ q) 0 + (y - x) from
        max_le (by linarith [le_max_left (x - uf P.c θ q) 0])
          (by linarith [le_max_right (x - uf P.c θ q) 0]))
    rw [integral_add (phi_int P θ x hθ0) (integrable_const _), integral_const] at h
    simpa [phi] using h
  have hnn : ∀ x, 0 ≤ phi P θ x := fun x => integral_nonneg fun q => le_max_right _ _
  have hφ : ∀ x, ∫ q, max (x + q - s q) 0 ∂(prePost (P.withδc d) (mass (Icc θ 1))) =
      phi P θ x := by
    intro x
    rw [hpp, phi]
    congr 1; funext q; simp only [hs]; ring_nf
  have heq : IsRespEq (P.withδc d) p₁ (Icc θ 1) s := by
    refine ⟨measurableSet_Icc, Icc_subset_Icc hθ0 le_rfl,
      (continuous_id.add (uf_cont _ _)).measurable, ?_, ?_, ?_⟩
    · intro q p
      simp only [secondProfit, lateMass_Icc θ _ _ hθ1]
      exact opt_u P.c θ q p hP.c_nonneg hθ0
    · intro x hx
      show 0 ≤ x - p₁ ∧ d * ∫ q, max (x + q - s q) 0 ∂(prePost (P.withδc d) (mass (Icc θ 1)))
        ≤ x - p₁
      rw [hφ, hp₁]
      have h1 := hlip θ x hx.1
      constructor
      · nlinarith [hnn θ, mul_nonneg hd0 (hnn θ), hx.1]
      · nlinarith [mul_le_mul_of_nonneg_left h1 hd0,
          mul_le_mul_of_nonneg_right hd1 (sub_nonneg.2 hx.1)]
    · intro x hx
      show x - p₁ ≤ d * ∫ q, max (x + q - s q) 0 ∂(prePost (P.withδc d) (mass (Icc θ 1)))
      rw [hφ, hp₁]
      have hxθ : x ≤ θ := by
        by_contra h; push Not at h; exact hx.2 ⟨h.le, hx.1.2⟩
      have h1 := hlip x θ hxθ
      nlinarith [mul_le_mul_of_nonneg_left h1 hd0,
          mul_le_mul_of_nonneg_right hd1 (sub_nonneg.2 hxθ)]
  have hprof : respProfit (P.withδc d) p₁ (Icc θ 1) s =
      (θ - d * phi P θ θ - P.c) * (1 - θ) + Gint P θ := by
    unfold respProfit
    rw [hpp, hmass]
    congr 1
    rw [Gint]
    congr 1; funext q
    obtain ⟨hu0, hu1⟩ := uf_bounds P.c θ q hθ0
    simp only [secondProfit, lateMass_Icc θ _ _ hθ1, hs]
    have e1 : q + uf P.c θ q - q = uf P.c θ q := by ring
    rw [e1, max_eq_right hu0, max_eq_left (by linarith)]
    show (q + uf P.c θ q - P.c) * (θ - uf P.c θ q) = _
    ring
  rw [← hprof]
  exact le_iSup (fun o : {o : ℝ × Set ℝ × (ℝ → ℝ) // IsRespEq (P.withδc d) o.1 o.2.1 o.2.2} =>
    ((respProfit (P.withδc d) o.1.1 o.1.2.1 o.1.2.2 : ℝ) : EReal)) ⟨(p₁, Icc θ 1, s), heq⟩

/-! ## Part 3: Gaussian estimates and pointwise bounds -/

lemma gauss_basic (v : ℝ≥0) :
    Integrable (fun q : ℝ => q) (gaussianReal 0 v) ∧
    Integrable (fun q : ℝ => q ^ 2) (gaussianReal 0 v) ∧
    ∫ q, q ∂(gaussianReal 0 v) = 0 ∧ ∫ q, q ^ 2 ∂(gaussianReal 0 v) = v := by
  have h1 : Integrable (fun q : ℝ => q) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal' (μ := 0) (v := v) 1 (by norm_num)).integrable le_rfl
  have h2 : MemLp (fun q : ℝ => q) 2 (gaussianReal 0 v) :=
    memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by norm_num)
  have hmean : ∫ q, q ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  refine ⟨h1, h2.integrable_sq, hmean, ?_⟩
  have := variance_of_integral_eq_zero (X := fun q : ℝ => q) aemeasurable_id hmean
  rw [variance_fun_id_gaussianReal] at this
  exact this.symm

lemma min_int (v : ℝ≥0) (t : ℝ) :
    Integrable (fun q : ℝ => min (q ^ 2) (t ^ 2)) (gaussianReal 0 v) := by
  refine Integrable.of_bound
    (((continuous_pow 2).min continuous_const).aestronglyMeasurable) (t ^ 2)
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact min_le_right _ _

lemma gauss_min_pos (v : ℝ≥0) (hv : v ≠ 0) (t : ℝ) (ht : 0 < t) :
    0 < ∫ q, min (q ^ 2) (t ^ 2) ∂(gaussianReal 0 v) := by
  rw [integral_pos_iff_support_of_nonneg (fun q => by simp only [Pi.zero_apply]; positivity)
    (min_int v t)]
  have hsupp : Ioi (0:ℝ) ⊆ Function.support (fun q : ℝ => min (q ^ 2) (t ^ 2)) := by
    intro q hq
    simp only [Function.mem_support]
    exact (lt_min (by have : (0:ℝ) < q := hq; positivity) (by positivity)).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsupp)
  rw [pos_iff_ne_zero]
  intro h0
  have := gaussianReal_absolutelyContinuous' 0 hv h0
  simp at this

lemma gauss_q4 (v : ℝ≥0) (hv : 0 < (v : ℝ)) :
    Integrable (fun q : ℝ => q ^ 4) (gaussianReal 0 v) ∧
    ∫ q, q ^ 4 ∂(gaussianReal 0 v) ≤ 96 * (v : ℝ) ^ 2 := by
  set l := 1 / Real.sqrt v with hl
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hl2 : l ^ 2 * v = 1 := by
    rw [hl, div_pow, Real.sq_sqrt hv.le]; field_simp
  have hE : ∀ r : ℝ, ∫ q, Real.exp (r * q) ∂(gaussianReal 0 v) = Real.exp (v * r ^ 2 / 2) := by
    intro r
    have := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) r
    simpa [mgf] using this
  have hexp : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hpt : ∀ q : ℝ, q ^ 4 ≤ 24 * (v : ℝ) ^ 2 * (Real.exp (l * q) + Real.exp ((-l) * q)) := by
    intro q
    have h1 := Real.pow_div_factorial_le_exp (|l * q|) (abs_nonneg (l * q)) 4
    have h2 : Real.exp (|l * q|) ≤ Real.exp (l * q) + Real.exp ((-l) * q) := by
      rcases abs_cases (l * q) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; linarith [Real.exp_pos ((-l) * q)]
      · rw [h, neg_mul]; linarith [Real.exp_pos (l * q)]
    have h3 : |l * q| ^ 4 = l ^ 4 * q ^ 4 := by
      rw [show |l * q| ^ 4 = (|l * q| ^ 2) ^ 2 by ring, sq_abs]; ring
    have h4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [h3, h4] at h1
    have e : q ^ 4 = (v : ℝ) ^ 2 * (l ^ 4 * q ^ 4) := by
      calc q ^ 4 = (l ^ 2 * v) ^ 2 * q ^ 4 := by rw [hl2]; ring
        _ = (v : ℝ) ^ 2 * (l ^ 4 * q ^ 4) := by ring
    rw [e]
    have : l ^ 4 * q ^ 4 ≤ 24 * (Real.exp (l * q) + Real.exp ((-l) * q)) := by linarith
    nlinarith [sq_nonneg (v : ℝ)]
  have hb : Integrable (fun q : ℝ => 24 * (v : ℝ) ^ 2 * (Real.exp (l * q) + Real.exp ((-l) * q)))
      (gaussianReal 0 v) :=
    ((integrable_exp_mul_gaussianReal l).add (integrable_exp_mul_gaussianReal (-l))).const_mul _
  have hi : Integrable (fun q : ℝ => q ^ 4) (gaussianReal 0 v) := by
    refine hb.mono' ((continuous_pow 4).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt q
  refine ⟨hi, ?_⟩
  have := integral_mono hi hb hpt
  rw [integral_const_mul, integral_add (integrable_exp_mul_gaussianReal l)
    (integrable_exp_mul_gaussianReal (-l)), hE, hE] at this
  have e2 : (v : ℝ) * l ^ 2 / 2 = 1 / 2 := by linarith [hl2]
  have e3 : (v : ℝ) * (-l) ^ 2 / 2 = 1 / 2 := by rw [neg_sq]; linarith
  rw [e2, e3] at this
  nlinarith [sq_nonneg (v : ℝ)]

lemma G_lower (c θ q : ℝ) (hc : 0 ≤ c) (hcθ : c < θ) :
    (θ - c) ^ 2 / 4 + (θ - c) / 2 * q + min (q ^ 2) ((θ - c) ^ 2) / 4 ≤
      (uf c θ q + q - c) * (θ - uf c θ q) := by
  have hθ : 0 ≤ θ := by linarith
  have hm1 := min_le_left (q ^ 2) ((θ - c) ^ 2)
  have hm2 := min_le_right (q ^ 2) ((θ - c) ^ 2)
  rcases uf_cases c θ q hθ with ⟨hw, hu⟩ | ⟨hw, hu⟩ | ⟨hw0, hw1, hu⟩ <;> rw [hu]
  · nlinarith [mul_nonneg (show 0 ≤ q - θ - c by linarith) (show 0 ≤ θ + c by linarith),
      mul_nonneg hθ hc]
  · nlinarith [mul_nonneg (show 0 ≤ θ - c by linarith) (show 0 ≤ -(θ - c + q) by linarith)]
  · nlinarith

lemma A_upper (c θ q : ℝ) (hc : 0 ≤ c) (hcθ : c < θ) :
    max (θ - uf c θ q) 0 ≤ (θ - c + q) / 2 + q ^ 2 / (8 * (θ - c)) := by
  have hθ : 0 ≤ θ := by linarith
  have ht : 0 < θ - c := by linarith
  obtain ⟨hu0, hu1⟩ := uf_bounds c θ q hθ
  rw [max_eq_left (show 0 ≤ θ - uf c θ q by linarith)]
  have hr0 : 0 ≤ q ^ 2 / (8 * (θ - c)) := by positivity
  have hr8 : q ^ 2 / (8 * (θ - c)) * (8 * (θ - c)) = q ^ 2 := div_mul_cancel₀ _ (by positivity)
  rcases uf_cases c θ q hθ with ⟨hw, hu⟩ | ⟨hw, hu⟩ | ⟨hw0, hw1, hu⟩ <;> rw [hu]
  · linarith
  · nlinarith [sq_nonneg (q + 2 * (θ - c))]
  · linarith

lemma min_lower (q t : ℝ) (ht : 0 < t) : q ^ 2 - q ^ 4 / (4 * t ^ 2) ≤ min (q ^ 2) (t ^ 2) := by
  have hr0 : 0 ≤ q ^ 4 / (4 * t ^ 2) := by positivity
  have hr4 : q ^ 4 / (4 * t ^ 2) * (4 * t ^ 2) = q ^ 4 := div_mul_cancel₀ _ (by positivity)
  rcases le_total (q ^ 2) (t ^ 2) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; nlinarith [sq_nonneg (q ^ 2 - 2 * t ^ 2), pow_pos ht 2]

lemma G_int (P : Params) (hP : P.Standing) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun q => (uf P.c θ q + q - P.c) * (θ - uf P.c θ q))
      (gaussianReal 0 (preVar P (1 - θ))) := by
  obtain ⟨h1, -⟩ := gauss_basic (preVar P (1 - θ))
  have hb : Integrable (fun q : ℝ => θ * (|q| + (θ + P.c))) (gaussianReal 0 (preVar P (1 - θ))) :=
    (h1.abs.add (integrable_const (θ + P.c))).const_mul θ
  refine hb.mono' (Continuous.aestronglyMeasurable
    ((((uf_cont _ _).add continuous_id).sub continuous_const).mul
      (continuous_const.sub (uf_cont _ _)))) (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨hu0, hu1⟩ := uf_bounds P.c θ q hθ
  have hc := hP.c_nonneg
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ θ - uf P.c θ q by linarith)]
  have hA : |uf P.c θ q + q - P.c| ≤ |q| + (θ + P.c) := by
    rw [abs_le]; constructor <;> linarith [neg_abs_le q, le_abs_self q]
  nlinarith [mul_le_mul hA (show θ - uf P.c θ q ≤ θ by linarith) (by linarith)
    (by positivity : (0:ℝ) ≤ |q| + (θ + P.c))]

lemma Gint_ge (P : Params) (hP : P.Standing) (θ : ℝ) (hcθ : P.c < θ) :
    (θ - P.c) ^ 2 / 4 +
      (∫ q, min (q ^ 2) ((θ - P.c) ^ 2) ∂(gaussianReal 0 (preVar P (1 - θ)))) / 4 ≤ Gint P θ := by
  have hθ : 0 ≤ θ := by linarith [hP.c_nonneg]
  obtain ⟨h1, -, hm, -⟩ := gauss_basic (preVar P (1 - θ))
  have hmin := min_int (preVar P (1 - θ)) (θ - P.c)
  have hA : Integrable (fun q : ℝ => (θ - P.c) ^ 2 / 4 + (θ - P.c) / 2 * q)
      (gaussianReal 0 (preVar P (1 - θ))) := (integrable_const _).add (h1.const_mul _)
  have hL : Integrable (fun q : ℝ => (θ - P.c) ^ 2 / 4 + (θ - P.c) / 2 * q +
      min (q ^ 2) ((θ - P.c) ^ 2) / 4) (gaussianReal 0 (preVar P (1 - θ))) :=
    hA.add (hmin.div_const _)
  have h := integral_mono hL (G_int P hP θ hθ) (fun q => G_lower P.c θ q hP.c_nonneg hcθ)
  rw [integral_add hA (hmin.div_const _), integral_add (integrable_const _) (h1.const_mul _),
    integral_const_mul, hm] at h
  have e : ∫ q, min (q ^ 2) ((θ - P.c) ^ 2) / 4 ∂(gaussianReal 0 (preVar P (1 - θ))) =
      (∫ q, min (q ^ 2) ((θ - P.c) ^ 2) ∂(gaussianReal 0 (preVar P (1 - θ)))) / 4 :=
    integral_div _ _
  unfold Gint
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul, mul_zero, add_zero] at h
  linarith

lemma Gint_ge1 (P : Params) (hP : P.Standing) (θ : ℝ) (hcθ : P.c < θ)
    (hv : 0 < (preVar P (1 - θ) : ℝ)) :
    (θ - P.c) ^ 2 / 4 + (preVar P (1 - θ) : ℝ) / 4 -
      6 * (preVar P (1 - θ) : ℝ) ^ 2 / (θ - P.c) ^ 2 ≤ Gint P θ := by
  have hθ : 0 ≤ θ := by linarith [hP.c_nonneg]
  have ht : 0 < θ - P.c := by linarith
  obtain ⟨h1, h2, hm, hm2⟩ := gauss_basic (preVar P (1 - θ))
  obtain ⟨h4, hm4⟩ := gauss_q4 (preVar P (1 - θ)) hv
  set t := θ - P.c with htdef
  set v : ℝ := (preVar P (1 - θ) : ℝ) with hvdef
  have hA : Integrable (fun q : ℝ => t ^ 2 / 4 + t / 2 * q)
      (gaussianReal 0 (preVar P (1 - θ))) := (integrable_const _).add (h1.const_mul _)
  have hB : Integrable (fun q : ℝ => 1 / 4 * q ^ 2 - 1 / (16 * t ^ 2) * q ^ 4)
      (gaussianReal 0 (preVar P (1 - θ))) := (h2.const_mul _).sub (h4.const_mul _)
  have hL : Integrable (fun q : ℝ => t ^ 2 / 4 + t / 2 * q +
      (1 / 4 * q ^ 2 - 1 / (16 * t ^ 2) * q ^ 4)) (gaussianReal 0 (preVar P (1 - θ))) :=
    hA.add hB
  have hpt : ∀ q, t ^ 2 / 4 + t / 2 * q + (1 / 4 * q ^ 2 - 1 / (16 * t ^ 2) * q ^ 4) ≤
      (uf P.c θ q + q - P.c) * (θ - uf P.c θ q) := by
    intro q
    have g1 := G_lower P.c θ q hP.c_nonneg hcθ
    have g2 := min_lower q t ht
    have e : 1 / 4 * q ^ 2 - 1 / (16 * t ^ 2) * q ^ 4 = (q ^ 2 - q ^ 4 / (4 * t ^ 2)) / 4 := by
      field_simp; ring
    rw [e]; linarith
  have h := integral_mono hL (G_int P hP θ hθ) hpt
  rw [integral_add hA hB, integral_add (integrable_const _) (h1.const_mul _),
    integral_sub (h2.const_mul _) (h4.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, hm, hm2] at h
  have hq : 1 / (16 * t ^ 2) * ∫ q, q ^ 4 ∂(gaussianReal 0 (preVar P (1 - θ))) ≤
      6 * v ^ 2 / t ^ 2 := by
    have := mul_le_mul_of_nonneg_left hm4 (show 0 ≤ 1 / (16 * t ^ 2) by positivity)
    have e : 1 / (16 * t ^ 2) * (96 * v ^ 2) = 6 * v ^ 2 / t ^ 2 := by field_simp; ring
    linarith
  unfold Gint
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul] at h
  linarith

lemma phi_le_theta (P : Params) (θ : ℝ) (hθ : 0 ≤ θ) : phi P θ θ ≤ θ := by
  have := integral_mono (phi_int P θ θ hθ) (integrable_const θ)
    (fun q => show max (θ - uf P.c θ q) 0 ≤ θ from
      max_le (by linarith [(uf_bounds P.c θ q hθ).1]) hθ)
  simpa [phi] using this

lemma phi_le1 (P : Params) (hP : P.Standing) (θ : ℝ) (hcθ : P.c < θ) :
    phi P θ θ ≤ (θ - P.c) / 2 + (preVar P (1 - θ) : ℝ) / (8 * (θ - P.c)) := by
  have hθ : 0 ≤ θ := by linarith [hP.c_nonneg]
  obtain ⟨h1, h2, hm, hm2⟩ := gauss_basic (preVar P (1 - θ))
  have hA : Integrable (fun q : ℝ => (θ - P.c) / 2 + 1 / 2 * q)
      (gaussianReal 0 (preVar P (1 - θ))) := (integrable_const _).add (h1.const_mul _)
  have hL : Integrable (fun q : ℝ => (θ - P.c) / 2 + 1 / 2 * q + 1 / (8 * (θ - P.c)) * q ^ 2)
      (gaussianReal 0 (preVar P (1 - θ))) := hA.add (h2.const_mul _)
  have h := integral_mono (phi_int P θ θ hθ) hL (fun q => by
    have := A_upper P.c θ q hP.c_nonneg hcθ
    have e : (θ - P.c + q) / 2 + q ^ 2 / (8 * (θ - P.c)) =
        (θ - P.c) / 2 + 1 / 2 * q + 1 / (8 * (θ - P.c)) * q ^ 2 := by ring
    simp only
    linarith)
  rw [integral_add hA (h2.const_mul _), integral_add (integrable_const _) (h1.const_mul _),
    integral_const_mul, integral_const_mul, hm, hm2] at h
  unfold phi
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul] at h
  have e : 1 / (8 * (θ - P.c)) * (preVar P (1 - θ) : ℝ) =
      (preVar P (1 - θ) : ℝ) / (8 * (θ - P.c)) := by ring
  linarith

lemma preVar_pos (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) (ε : ℝ) (hε : 0 < ε) :
    (preVar P ε : ℝ) = P.σp ^ 2 * (ε * P.γ / (ε * P.γ + 1)) ∧ 0 < (preVar P ε : ℝ) := by
  have hpos : 0 < P.σp ^ 2 * (ε * P.γ / (ε * P.γ + 1)) :=
    mul_pos (pow_pos hP.σp_pos 2) (div_pos (mul_pos hε hγ) (by nlinarith [mul_pos hε hγ]))
  have e : (preVar P ε : ℝ) = P.σp ^ 2 * (ε * P.γ / (ε * P.γ + 1)) := by
    simp only [preVar]; exact Real.coe_toNNReal _ hpos.le
  exact ⟨e, e ▸ hpos⟩

/-! ## Part 4: the two ends -/

lemma near0 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    ∃ Δ ∈ Ioc (0:ℝ) 1, ∀ d ∈ Icc (0:ℝ) 1, d ≤ Δ →
      (((1 - P.c) ^ 2 / 3 : ℝ) : EReal) < respValue (P.withδc d) := by
  have hc0 := hP.c_nonneg
  have hc1 := hP.c_lt_one
  set a := 1 - P.c with ha
  have ha0 : 0 < a := by linarith
  set θ := P.c + 2 * a / 3 with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  have hcθ : P.c < θ := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have e1 : 1 - θ = a / 3 := by linarith
  have e2 : θ - P.c = 2 * a / 3 := by linarith
  obtain ⟨-, hvpos⟩ := preVar_pos P hP hγ (1 - θ) h1θ
  have hv0 : preVar P (1 - θ) ≠ 0 := by
    intro h; rw [h] at hvpos; simp at hvpos
  have hIpos := gauss_min_pos (preVar P (1 - θ)) hv0 (θ - P.c) (by linarith)
  set I := ∫ q, min (q ^ 2) ((θ - P.c) ^ 2) ∂(gaussianReal 0 (preVar P (1 - θ))) with hI
  have hG := Gint_ge P hP θ hcθ
  rw [← hI, e2] at hG
  refine ⟨min 1 (I / 8), ⟨lt_min one_pos (by linarith), min_le_left _ _⟩, fun d hd hdΔ => ?_⟩
  have hdI : d ≤ I / 8 := hdΔ.trans (min_le_right _ _)
  have hφ1 : phi P θ θ ≤ 1 := (phi_le_theta P θ hθ0).trans hθ1
  have hφ0 : 0 ≤ phi P θ θ := integral_nonneg fun q => le_max_right _ _
  set X := d * phi P θ θ with hX
  have hX0 : 0 ≤ X := mul_nonneg hd.1 hφ0
  have hXd : X ≤ d := by nlinarith [hd.1]
  have hreal : (1 - P.c) ^ 2 / 3 < (θ - X - P.c) * (1 - θ) + Gint P θ := by
    have k1 : (θ - X - P.c) * (1 - θ) = (2 * a / 3 - X) * (a / 3) := by
      rw [e1, show θ - X - P.c = (θ - P.c) - X by ring, e2]
    rw [k1, ← ha]
    have k2 : X * a ≤ X := mul_le_of_le_one_right hX0 (by linarith)
    nlinarith
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hreal) (SL_value_ge P hP d θ hd.1 hd.2 hθ0 hθ1)

lemma near1_arith (a k ε t v φ G d : ℝ) (ha0 : 0 < a) (hk0 : 0 < k) (hε0 : 0 < ε)
    (hε1 : ε ≤ a / 4) (hkε : k * ε ≤ a ^ 2 / 384) (hε3 : ε ≤ k / 8) (hta : t = a - ε)
    (hvpos : 0 < v) (hvle : v ≤ k * ε) (hvge : k * ε / 2 ≤ v)
    (hφ : φ ≤ t / 2 + v / (8 * t)) (hφ0 : 0 ≤ φ)
    (hG : t ^ 2 / 4 + v / 4 - 6 * v ^ 2 / t ^ 2 ≤ G)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (h1d : (1 - d) * a ^ 2 ≤ k * ε / 8) :
    a ^ 2 / 4 + (1 - d) * a ^ 2 / 8 < (t - d * φ) * ε + G := by
  have ht0 : 0 < t := by linarith
  have hA : v / (8 * t) * ε ≤ v / 16 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left (show 2 * ε ≤ t by linarith) hvpos.le]
  have hB : 6 * v ^ 2 / t ^ 2 ≤ v / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h96 : 96 * v ≤ t ^ 2 := by
      nlinarith [mul_self_le_mul_self (by linarith : (0:ℝ) ≤ 3 * a / 4)
        (show 3 * a / 4 ≤ t by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h96 hvpos.le]
  have hC : ε ^ 2 / 4 ≤ k * ε / 32 := by nlinarith [mul_le_mul_of_nonneg_left hε3 hε0.le]
  have m1 := mul_le_mul_of_nonneg_right hφ hε0.le
  have hdφ : d * φ ≤ φ := by nlinarith
  have m2 := mul_le_mul_of_nonneg_right hdφ hε0.le
  have ha2 : a ^ 2 = t ^ 2 + 2 * t * ε + ε ^ 2 := by rw [hta]; ring
  have e1 : (t / 2 + v / (8 * t)) * ε = t * ε / 2 + v / (8 * t) * ε := by ring
  nlinarith [mul_pos hk0 hε0]

set_option maxHeartbeats 1000000 in
lemma near1 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    ∃ Δ ∈ Ico (0:ℝ) 1, ∀ d ∈ Icc (0:ℝ) 1, Δ ≤ d →
      (((1 - P.c) ^ 2 / 4 + (1 - d) * (1 - P.c) ^ 2 / 8 : ℝ) : EReal) <
        respValue (P.withδc d) := by
  have hc0 := hP.c_nonneg
  have hc1 := hP.c_lt_one
  obtain ⟨a, ha⟩ : ∃ a, a = 1 - P.c := ⟨_, rfl⟩
  have ha0 : 0 < a := by linarith
  obtain ⟨k, hk⟩ : ∃ k, k = P.σp ^ 2 * P.γ := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; exact mul_pos (pow_pos hP.σp_pos 2) hγ
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min (min (a / 4) (a ^ 2 / (384 * k))) (min (k / 8) (1 / P.γ)) :=
    ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]
    exact lt_min (lt_min (by linarith) (by positivity)) (lt_min (by linarith) (by positivity))
  have hε1 : ε ≤ a / 4 := by rw [hε]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ a ^ 2 / (384 * k) := by rw [hε]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ k / 8 := by rw [hε]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hε4 : ε ≤ 1 / P.γ := by rw [hε]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hθ0 : 0 ≤ 1 - ε := by linarith
  have hθ1 : 1 - ε ≤ 1 := by linarith
  have hcθ : P.c < 1 - ε := by linarith
  have e1 : 1 - (1 - ε) = ε := by ring
  obtain ⟨hve, hvpos⟩ := preVar_pos P hP hγ ε hε0
  have hφ := phi_le1 P hP (1 - ε) hcθ
  have hG := Gint_ge1 P hP (1 - ε) hcθ (by rw [e1]; exact hvpos)
  rw [e1] at hφ hG
  have hta : 1 - ε - P.c = a - ε := by rw [ha]; ring
  rw [hta] at hφ hG
  have hεγ : ε * P.γ ≤ 1 := by
    rw [le_div_iff₀ hγ] at hε4; linarith
  have hεγ0 : 0 ≤ ε * P.γ := (mul_pos hε0 hγ).le
  have hfrac1 : ε * P.γ / (ε * P.γ + 1) ≤ ε * P.γ := div_le_self hεγ0 (by linarith)
  have hfrac2 : ε * P.γ / 2 ≤ ε * P.γ / (ε * P.γ + 1) :=
    div_le_div_of_nonneg_left hεγ0 (by linarith) (by linarith)
  have hvle : (preVar P ε : ℝ) ≤ k * ε := by
    rw [hve, hk]; nlinarith [mul_le_mul_of_nonneg_left hfrac1 (sq_nonneg P.σp)]
  have hvge : k * ε / 2 ≤ (preVar P ε : ℝ) := by
    rw [hve, hk]; nlinarith [mul_le_mul_of_nonneg_left hfrac2 (sq_nonneg P.σp)]
  have hkε : k * ε ≤ a ^ 2 / 384 := by
    rw [le_div_iff₀ (by positivity)] at hε2
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have hm0 : 0 < k * ε / (8 * a ^ 2) := by positivity
  refine ⟨max 0 (1 - k * ε / (8 * a ^ 2)), ⟨le_max_left _ _, max_lt one_pos (by linarith)⟩,
    fun d hd hdΔ => ?_⟩
  have h1d : 1 - d ≤ k * ε / (8 * a ^ 2) := by
    linarith [le_max_right 0 (1 - k * ε / (8 * a ^ 2))]
  have h1d' : (1 - d) * a ^ 2 ≤ k * ε / 8 := by
    rw [le_div_iff₀ (by positivity)] at h1d; linarith
  have hφ0 : 0 ≤ phi P (1 - ε) (1 - ε) := integral_nonneg fun q => le_max_right _ _
  have hreal := near1_arith a k ε (a - ε) (preVar P ε) (phi P (1 - ε) (1 - ε)) (Gint P (1 - ε)) d
    ha0 hk0 hε0 hε1 hkε hε3 rfl hvpos hvle hvge hφ hφ0 hG hd.1 hd.2 h1d'
  have key := SL_value_ge P hP d (1 - ε) hd.1 hd.2 hθ0 hθ1
  rw [e1] at key
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 ?_) key
  rw [← ha]
  have e2 : 1 - ε - d * phi P (1 - ε) (1 - ε) - P.c = a - ε - d * phi P (1 - ε) (1 - ε) := by
    rw [ha]; ring
  rw [e2]; exact hreal

end SLPricing.Resp.P6

open MeasureTheory ProbabilityTheory Set SLPricing.Resp in
theorem solution (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    ∃ Δlr ∈ Ioc (0 : ℝ) 1, ∃ Δhr ∈ Ico (0 : ℝ) 1, ∀ d ∈ Icc (0 : ℝ) 1, (d ≤ Δlr ∨ Δhr ≤ d) →
      respValue (P.withδc d).noSL < respValue (P.withδc d) := by
  obtain ⟨Δ0, hΔ0, h0⟩ := SLPricing.Resp.P6.near0 P hP hγ
  obtain ⟨Δ1, hΔ1, h1⟩ := SLPricing.Resp.P6.near1 P hP hγ
  refine ⟨Δ0, hΔ0, Δ1, hΔ1, fun d hd hor => ?_⟩
  obtain ⟨b1, b2⟩ := SLPricing.Resp.P6.noSL_value_le P hP d hd.1 hd.2
  rcases hor with h | h
  · exact lt_of_le_of_lt b1 (h0 d hd h)
  · exact lt_of_le_of_lt b2 (h1 d hd h)
