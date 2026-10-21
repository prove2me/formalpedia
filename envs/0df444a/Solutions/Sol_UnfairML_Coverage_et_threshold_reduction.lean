-- Prove2me | solution 1 for UnfairML.Coverage.et_threshold_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T05:43:42.846215+00:00
-- url     : https://prove2.me/submissions/8af477b9-0791-4ce0-b0a1-7d214d6cf71e

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

open UnfairML.Coverage

namespace UF2Lib

lemma facts (P : Params) (hS : P.Standing) :
    0 < P.αp ∧ 0 < P.βp ∧ 0 < P.αr ∧ P.αr ≤ P.βr ∧ P.αp < P.βp ∧ 0 < P.γp ∧ P.γp < P.γr ∧
    0 < P.γr := by
  obtain ⟨hα, hβ, hdr, hdrp, hdp, hab, hgp, hgpr⟩ := hS
  simp only [Params.αp, Params.βp, Params.αr, Params.βr] at *
  refine ⟨mul_pos hα (by linarith), mul_pos hβ (by linarith), mul_pos hα (by linarith), hab,
    ?_, hgp, hgpr, by linarith⟩
  have : (P.α + P.β) * (P.dp - P.dr) > 0 := mul_pos (by linarith) (by linarith)
  nlinarith

lemma rho_bounds (P : Params) (hS : P.Standing) : 1 / 2 < P.rho ∧ P.rho < 1 := by
  obtain ⟨-, -, -, -, -, hgp, hgpr, hgr⟩ := facts P hS
  have h1 : P.γp / P.γr < 1 := (div_lt_one hgr).2 hgpr
  have h0 : 0 < P.γp / P.γr := div_pos hgp hgr
  unfold Params.rho
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; linarith
  · rw [div_lt_one (by linarith)]; linarith

lemma rho_eq (P : Params) (hS : P.Standing) : P.rho = P.γr / (2 * P.γr - P.γp) := by
  obtain ⟨-, -, -, -, -, hgp, hgpr, hgr⟩ := facts P hS
  unfold Params.rho
  have : 2 * P.γr - P.γp ≠ 0 := by linarith
  field_simp

lemma s_bounds (P : Params) (hS : P.Standing) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) :
    0 ≤ s ∧ 0 ≤ P.γp * s ∧ P.γp * s ≤ P.γr * s ∧ P.γr * s ≤ 1 / 2 := by
  obtain ⟨-, -, -, -, -, hgp, hgpr, hgr⟩ := facts P hS
  obtain ⟨h0, h1⟩ := hs
  unfold Params.sMax at h1
  have : P.γr * s ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  exact ⟨h0, by positivity, by nlinarith, this⟩

lemma Acoef_pos (P : Params) (hS : P.Standing) (k σ : ℝ) (hC : CostRange P k σ) :
    0 < P.Acoef := by
  have hr := rho_bounds P hS
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hC
  by_contra h
  push Not at h
  have hσ0 : 0 < σ := by linarith
  have h1s : 0 ≤ 1 - σ ^ 2 := by nlinarith
  have : σ ^ 2 * P.Acoef ≥ P.Acoef := by nlinarith [mul_nonneg h1s (neg_nonneg.2 h)]
  linarith

/-- The generic profit shape `F_q(s) = s/(1 − p s) − q² s/(1 − r s)`. -/
noncomputable def F (p r q s : ℝ) : ℝ := s / (1 - p * s) - q ^ 2 * s / (1 - r * s)

/-- Its unique maximizer `s* = (1 − q)/(r − p q)`. -/
noncomputable def sstar (p r q : ℝ) : ℝ := (1 - q) / (r - p * q)

lemma gap (p r q s : ℝ) (hp : 0 < p) (hpr : p < r) (hq0 : 0 < q) (hq1 : q < 1)
    (hs0 : 0 ≤ s) (hs1 : r * s < 1) :
    F p r q (sstar p r q) - F p r q s =
      (1 - q - (r - p * q) * s) ^ 2 / ((r - p) * (1 - p * s) * (1 - r * s)) := by
  have h1 : r - p * q > 0 := by nlinarith
  have h2 : 1 - p * s > 0 := by nlinarith
  have h3 : 1 - r * s > 0 := by linarith
  have h4 : r - p > 0 := by linarith
  have h1' : r - p * q ≠ 0 := ne_of_gt h1
  have h2' : 1 - p * s ≠ 0 := ne_of_gt h2
  have h3' : 1 - r * s ≠ 0 := ne_of_gt h3
  have h4' : r - p ≠ 0 := ne_of_gt h4
  have hq' : q ≠ 0 := ne_of_gt hq0
  unfold F sstar
  obtain ⟨w, hw⟩ : ∃ w, w = r - p * q := ⟨_, rfl⟩
  rw [← hw]
  have hw' : w ≠ 0 := by rw [hw]; exact h1'
  have e1 : 1 - p * ((1 - q) / w) = (r - p) / w := by
    rw [eq_div_iff hw', sub_mul, mul_assoc, div_mul_cancel₀ _ hw', hw]; ring
  have e2 : 1 - r * ((1 - q) / w) = q * (r - p) / w := by
    rw [eq_div_iff hw', sub_mul, mul_assoc, div_mul_cancel₀ _ hw', hw]; ring
  rw [e1, e2]
  field_simp
  subst hw
  ring

lemma sstar_mem (p r q : ℝ) (hp : 0 < p) (hpr : p < r) (hq1 : q < 1)
    (hq : r / (2 * r - p) ≤ q) :
    0 < sstar p r q ∧ sstar p r q ≤ 1 / (2 * r) := by
  have hr : 0 < r := by linarith
  have h2 : 0 < 2 * r - p := by linarith
  rw [div_le_iff₀ h2] at hq
  have hq0 : 0 < q := by nlinarith
  have h1 : r - p * q > 0 := by nlinarith
  unfold sstar
  refine ⟨div_pos (by linarith) h1, ?_⟩
  rw [div_le_div_iff₀ h1 (by positivity)]
  nlinarith

lemma sstar_lt (p r q : ℝ) (hp : 0 < p) (hpr : p < r) (hq1 : q < 1)
    (hq : r / (2 * r - p) < q) :
    sstar p r q < 1 / (2 * r) := by
  have hr : 0 < r := by linarith
  have h2 : 0 < 2 * r - p := by linarith
  rw [div_lt_iff₀ h2] at hq
  have hq0 : 0 < q := by nlinarith
  have h1 : r - p * q > 0 := by nlinarith
  unfold sstar
  rw [div_lt_div_iff₀ h1 (by positivity)]
  nlinarith

/-- Every maximizer on `[0, 1/(2r)]` of `c · F_q` (with `c > 0`) equals `s*`. -/
lemma max_unique (p r q c : ℝ) (hp : 0 < p) (hpr : p < r) (hq1 : q < 1)
    (hq : r / (2 * r - p) ≤ q) (hc : 0 < c) (f : ℝ → ℝ)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) (1 / (2 * r)), f s = c * F p r q s)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (1 / (2 * r)))
    (hmax : IsMaxOn f (Set.Icc 0 (1 / (2 * r))) s) : s = sstar p r q := by
  have hr : 0 < r := by linarith
  have h2 : 0 < 2 * r - p := by linarith
  have hq' := hq
  rw [div_le_iff₀ h2] at hq'
  have hq0 : 0 < q := by nlinarith
  obtain ⟨hm0, hm1⟩ := sstar_mem p r q hp hpr hq1 hq
  have hmem : sstar p r q ∈ Set.Icc (0 : ℝ) (1 / (2 * r)) := ⟨hm0.le, hm1⟩
  have hle : f (sstar p r q) ≤ f s := hmax hmem
  rw [hf _ hmem, hf _ hs] at hle
  have hrs : r * s ≤ 1 / 2 := by
    have := hs.2; rw [le_div_iff₀ (by positivity)] at this; linarith
  have hg := gap p r q s hp hpr hq0 hq1 hs.1 (by linarith)
  have hFle : F p r q (sstar p r q) - F p r q s ≤ 0 := by
    have := (mul_le_mul_iff_of_pos_left hc).1 hle; linarith
  rw [hg] at hFle
  have hd : 0 < (r - p) * (1 - p * s) * (1 - r * s) := by
    have : 0 ≤ p * s := mul_nonneg hp.le hs.1
    have : p * s ≤ r * s := mul_le_mul_of_nonneg_right hpr.le hs.1
    exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hsq : (1 - q - (r - p * q) * s) ^ 2 ≤ 0 := by
    have := (div_le_iff₀ hd).1 hFle; linarith
  have hz : 1 - q - (r - p * q) * s = 0 := by nlinarith [sq_nonneg (1 - q - (r - p * q) * s)]
  have h1 : r - p * q ≠ 0 := by nlinarith
  unfold sstar
  rw [eq_div_iff h1]
  linarith

/-- `s* ` is a maximizer of `c · F_q` on `[0, 1/(2r)]`. -/
lemma sstar_isMax (p r q c : ℝ) (hp : 0 < p) (hpr : p < r) (hq1 : q < 1)
    (hq : r / (2 * r - p) ≤ q) (hc : 0 < c) (f : ℝ → ℝ)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) (1 / (2 * r)), f s = c * F p r q s) :
    IsMaxOn f (Set.Icc 0 (1 / (2 * r))) (sstar p r q) := by
  have hr : 0 < r := by linarith
  have h2 : 0 < 2 * r - p := by linarith
  have hq' := hq
  rw [div_le_iff₀ h2] at hq'
  have hq0 : 0 < q := by nlinarith
  obtain ⟨hm0, hm1⟩ := sstar_mem p r q hp hpr hq1 hq
  have hmem : sstar p r q ∈ Set.Icc (0 : ℝ) (1 / (2 * r)) := ⟨hm0.le, hm1⟩
  intro s hs
  show f s ≤ f (sstar p r q)
  rw [hf _ hmem, hf _ hs]
  have hrs : r * s ≤ 1 / 2 := by
    have := hs.2; rw [le_div_iff₀ (by positivity)] at this; linarith
  have hg := gap p r q s hp hpr hq0 hq1 hs.1 (by linarith)
  have hd : 0 < (r - p) * (1 - p * s) * (1 - r * s) := by
    have : 0 ≤ p * s := mul_nonneg hp.le hs.1
    have : p * s ≤ r * s := mul_le_mul_of_nonneg_right hpr.le hs.1
    exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have : 0 ≤ F p r q (sstar p r q) - F p r q s := by rw [hg]; positivity
  nlinarith

lemma piET_eq (P : Params) (k σ : ℝ) (hk : k = P.αr * P.γr + σ ^ 2 * P.Acoef) (s : ℝ) :
    piET P k s = P.Acoef * F P.γp P.γr σ s := by
  unfold piET F tau Params.Acoef at *
  subst hk
  simp only [div_eq_mul_inv]
  ring

/-- `D = k − αrγr + βpγr − αpγr`. -/
lemma piEO_eq (P : Params) (k q : ℝ) (hq : P.βp * P.γp * q ^ 2 =
    k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr) (s : ℝ) :
    piEO P k s = (P.βp * P.γp) * F P.γp P.γr q s := by
  unfold piEO F tau at *
  have : k = P.βp * P.γp * q ^ 2 + P.αr * P.γr - P.βp * P.γr + P.αp * P.γr := by linarith
  subst this
  simp only [div_eq_mul_inv]
  ring

/-- `D > 0` and `D < βpγp`, and `D > σ² βpγp`. -/
lemma D_bounds (P : Params) (hS : P.Standing) (k σ : ℝ) (hC : CostRange P k σ) :
    σ ^ 2 * (P.βp * P.γp) < k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr ∧
    k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr < P.βp * P.γp := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  have hA := Acoef_pos P hS k σ hC
  obtain ⟨-, ⟨h3, h4⟩, h5⟩ := hC
  have hr := rho_bounds P hS
  have hσ0 : 0 < σ := by linarith
  have h1s : 0 < 1 - σ ^ 2 := by nlinarith
  subst h5
  unfold Params.Acoef at *
  constructor
  · have : 0 < (1 - σ ^ 2) * ((P.βp - P.αp) * P.γr) := mul_pos h1s (mul_pos (by linarith) hgr)
    nlinarith
  · nlinarith

/-- `q = √(D/(βpγp))` lies in `(σ, 1)`. -/
lemma q_bounds (P : Params) (hS : P.Standing) (k σ : ℝ) (hC : CostRange P k σ) :
    let q := Real.sqrt ((k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr) / (P.βp * P.γp))
    σ < q ∧ q < 1 ∧ P.βp * P.γp * q ^ 2 = k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr := by
  intro q
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  obtain ⟨hD1, hD2⟩ := D_bounds P hS k σ hC
  have hr := rho_bounds P hS
  have hσ0 : 0 < σ := by have := hC.2.1.1; linarith
  have hb : 0 < P.βp * P.γp := mul_pos hβp hgp
  have hDpos : 0 < k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr := by nlinarith
  have hsq : q ^ 2 = (k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr) / (P.βp * P.γp) :=
    Real.sq_sqrt (div_pos hDpos hb).le
  refine ⟨?_, ?_, ?_⟩
  · rw [show σ = Real.sqrt (σ ^ 2) from (Real.sqrt_sq hσ0.le).symm]
    apply Real.sqrt_lt_sqrt (sq_nonneg _)
    rw [lt_div_iff₀ hb]; linarith
  · rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    apply Real.sqrt_lt_sqrt (div_pos hDpos hb).le
    rw [div_lt_one hb]; linarith
  · rw [hsq]; field_simp

end UF2Lib


open UnfairML.Coverage

namespace UF2Lib

lemma sMax_eq (P : Params) : P.sMax = 1 / (2 * P.γr) := rfl

lemma piET_on (P : Params) (k σ : ℝ) (hC : CostRange P k σ) :
    ∀ s ∈ Set.Icc (0 : ℝ) (1 / (2 * P.γr)), piET P k s = P.Acoef * F P.γp P.γr σ s :=
  fun s _ => piET_eq P k σ hC.2.2 s

lemma sigma_ge (P : Params) (hS : P.Standing) (k σ : ℝ) (hC : CostRange P k σ) :
    P.γr / (2 * P.γr - P.γp) ≤ σ := by
  rw [← rho_eq P hS]; exact hC.2.1.1

lemma sET_eq (P : Params) (hS : P.Standing) (k σ : ℝ) (hC : CostRange P k σ) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) (hmax : IsMaxOn (piET P k) (Set.Icc 0 P.sMax) s) :
    s = sstar P.γp P.γr σ := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  rw [sMax_eq] at hs hmax
  exact max_unique P.γp P.γr σ P.Acoef hgp hgpr hC.2.1.2 (sigma_ge P hS k σ hC)
    (Acoef_pos P hS k σ hC) _ (piET_on P k σ hC) s hs hmax

lemma eq51 (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) P.sMax)
    (hmax : IsMaxOn (piET P k) (Set.Icc 0 P.sMax) s) :
    P.γr * s / (1 - P.γp * s) =
      P.γr / (P.γr - P.γp) * (1 - Real.sqrt ((k - P.αr * P.γr) / P.Acoef)) := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  have hA := Acoef_pos P hS k σ hC
  have hr := rho_bounds P hS
  have hσ0 : 0 < σ := by have := hC.2.1.1; linarith
  have hσ1 := hC.2.1.2
  have hsq : Real.sqrt ((k - P.αr * P.γr) / P.Acoef) = σ := by
    rw [hC.2.2, show P.αr * P.γr + σ ^ 2 * P.Acoef - P.αr * P.γr = σ ^ 2 * P.Acoef by ring,
      mul_div_assoc, div_self hA.ne', mul_one, Real.sqrt_sq hσ0.le]
  rw [hsq, sET_eq P hS k σ hC s hs hmax]
  unfold sstar
  have h1 : P.γr - P.γp * σ ≠ 0 := by nlinarith
  have h1' : P.γr - σ * P.γp ≠ 0 := by nlinarith
  have h2 : P.γr - P.γp ≠ 0 := by linarith
  have e : 1 - P.γp * ((1 - σ) / (P.γr - P.γp * σ)) = (P.γr - P.γp) / (P.γr - P.γp * σ) := by
    rw [eq_div_iff h1, sub_mul, mul_assoc, div_mul_cancel₀ _ h1]; ring
  rw [e]
  field_simp

noncomputable def qEO (P : Params) (k : ℝ) : ℝ :=
  Real.sqrt ((k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr) / (P.βp * P.γp))

lemma piEO_on (P : Params) (hS : P.Standing) (k σ : ℝ) (hC : CostRange P k σ) :
    ∀ s ∈ Set.Icc (0 : ℝ) (1 / (2 * P.γr)),
      piEO P k s = (P.βp * P.γp) * F P.γp P.γr (qEO P k) s :=
  fun s _ => piEO_eq P k (qEO P k) (q_bounds P hS k σ hC).2.2 s

lemma q_ge (P : Params) (hS : P.Standing) (k σ : ℝ) (hC : CostRange P k σ) :
    P.γr / (2 * P.γr - P.γp) < qEO P k := by
  rw [← rho_eq P hS]
  exact lt_of_le_of_lt hC.2.1.1 (q_bounds P hS k σ hC).1

lemma sEO_eq (P : Params) (hS : P.Standing) (k σ : ℝ) (hC : CostRange P k σ) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) (hmax : IsMaxOn (piEO P k) (Set.Icc 0 P.sMax) s) :
    s = sstar P.γp P.γr (qEO P k) := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  rw [sMax_eq] at hs hmax
  exact max_unique P.γp P.γr (qEO P k) (P.βp * P.γp) hgp hgpr (q_bounds P hS k σ hC).2.1
    (q_ge P hS k σ hC).le (mul_pos hβp hgp) _ (piEO_on P hS k σ hC) s hs hmax

lemma eq52 (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) P.sMax)
    (hmax : IsMaxOn (piEO P k) (Set.Icc 0 P.sMax) s) :
    P.γr * s / (1 - P.γr * s) =
      P.γr / (P.γr - P.γp) *
        (Real.sqrt (P.βp * P.γp / (k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr)) - 1) := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  obtain ⟨hq1, hq2, hq3⟩ : σ < qEO P k ∧ qEO P k < 1 ∧
      P.βp * P.γp * qEO P k ^ 2 = k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr :=
    q_bounds P hS k σ hC
  have hr := rho_bounds P hS
  have hσ0 : 0 < σ := by have := hC.2.1.1; linarith
  set q := qEO P k with hqdef
  have hq0 : 0 < q := by linarith
  have hb : 0 < P.βp * P.γp := mul_pos hβp hgp
  have hinv : Real.sqrt (P.βp * P.γp / (k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr)) = 1 / q := by
    rw [← hq3, show P.βp * P.γp / (P.βp * P.γp * q ^ 2) = (1 / q) ^ 2 by field_simp,
      Real.sqrt_sq (by positivity)]
  rw [hinv, sEO_eq P hS k σ hC s hs hmax, ← hqdef]
  unfold sstar
  have h1 : P.γr - P.γp * q ≠ 0 := by nlinarith
  have h1' : P.γr - q * P.γp ≠ 0 := by nlinarith
  have h2 : P.γr - P.γp ≠ 0 := by linarith
  have e : 1 - P.γr * ((1 - q) / (P.γr - P.γp * q)) = q * (P.γr - P.γp) / (P.γr - P.γp * q) := by
    rw [eq_div_iff h1, sub_mul, mul_assoc, div_mul_cancel₀ _ h1]; ring
  rw [e]
  field_simp

lemma eq54 (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ) :
    P.γr / (P.γr - P.γp) * (1 - Real.sqrt ((k - P.αr * P.γr) / P.Acoef)) -
      P.γr / (P.γr - P.γp) *
        (Real.sqrt (P.βp * P.γp / (k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr)) - 1) =
    P.γr / (P.γr - P.γp) *
      (2 - σ - Real.sqrt (P.βp * P.γp /
        (σ ^ 2 * P.βp * P.γp + (1 - σ ^ 2) * (P.βp * P.γr - P.αp * P.γr)))) := by
  have hA := Acoef_pos P hS k σ hC
  have hr := rho_bounds P hS
  have hσ0 : 0 < σ := by have := hC.2.1.1; linarith
  have hsq : Real.sqrt ((k - P.αr * P.γr) / P.Acoef) = σ := by
    rw [hC.2.2, show P.αr * P.γr + σ ^ 2 * P.Acoef - P.αr * P.γr = σ ^ 2 * P.Acoef by ring,
      mul_div_assoc, div_self hA.ne', mul_one, Real.sqrt_sq hσ0.le]
  have hD : k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr =
      σ ^ 2 * P.βp * P.γp + (1 - σ ^ 2) * (P.βp * P.γr - P.αp * P.γr) := by
    rw [hC.2.2]; unfold Params.Acoef; ring
  rw [hsq, hD]; ring


/-- Common setup for the threshold reductions. -/
lemma thr_setup (P : Params) (hS : P.Standing) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) :
    0 < 1 - P.γp * s ∧ 0 < 1 - P.γr * s ∧ 1 / (1 - P.γp * s) ≤ 1 / (1 - P.γr * s) ∧
    0 < 1 / (1 - P.γp * s) ∧
    P.γr * s * (1 / (1 - P.γr * s)) ≤ 1 ∧ P.γr * s * (1 / (1 - P.γp * s)) ≤ 1 ∧
    P.γp * s * (1 / (1 - P.γp * s)) ≤ P.γr * s * (1 / (1 - P.γr * s)) := by
  obtain ⟨hs0, ha0, hab', hb⟩ := s_bounds P hS s hs
  have hda : 0 < 1 - P.γp * s := by linarith
  have hdb : 0 < 1 - P.γr * s := by linarith
  refine ⟨hda, hdb, one_div_le_one_div_of_le hdb (by linarith), by positivity, ?_, ?_, ?_⟩
  · rw [mul_one_div, div_le_one hdb]; linarith
  · rw [mul_one_div, div_le_one hda]; linarith
  · rw [mul_one_div, mul_one_div, div_le_div_iff₀ hda hdb]; nlinarith

lemma et_red (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k s c : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    profit P k c c s ≤ piET P k s ∧ (profit P k c c s = piET P k s ↔ c = 1 - P.γr * s) := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  obtain ⟨hs0, ha0, hab', hb⟩ := s_bounds P hS s hs
  obtain ⟨hda, hdb, hvu, hv, hbu, hbv, hav⟩ := thr_setup P hS s hs
  have hL' : P.βp ≤ P.αp + P.αr := hL
  unfold profit piET
  set τ := tau P k s
  set a := P.γp * s with ha
  set b := P.γr * s with hb'
  set u := 1 / (1 - b) with hu
  set v := 1 / (1 - a) with hv'
  have e1 : (1 - c) / (1 - b) = (1 - c) * u := by rw [hu, mul_one_div]
  have e2 : (1 - b - c) / (1 - b) = (1 - c - b) * u := by rw [hu, mul_one_div]; ring_nf
  have e3 : (1 - c) / (1 - a) = (1 - c) * v := by rw [hv', mul_one_div]
  have e4 : (1 - a - c) / (1 - a) = (1 - c - a) * v := by rw [hv', mul_one_div]; ring_nf
  have hpi : P.αp * P.γr * s / (1 - a) + P.αr * P.γr * s / (1 - b) + P.βp * P.γp * s / (1 - a)
      - P.βp * P.γr * s / (1 - a) - τ = P.αr * (b * u) + P.αp * (b * v) - P.βp * ((b - a) * v) - τ := by
    rw [hu, hv', hb', ha]; field_simp; ring
  rw [e1, e2, e3, e4, hpi]
  set x := 1 - c with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith [hc.2]
  have hm1 := min_le_left (x * u) 1
  have hm2 := min_le_left (x * v) 1
  have hM1a := le_max_left ((x - b) * u) 0
  have hM1b := le_max_right ((x - b) * u) 0
  have hM2a := le_max_left ((x - a) * v) 0
  have hM2b := le_max_right ((x - a) * v) 0
  set m1 := min (x * u) 1
  set m2 := min (x * v) 1
  set M1 := max ((x - b) * u) 0
  set M2 := max ((x - a) * v) 0
  have k1 : P.αr * m1 ≤ P.αr * (x * u) := mul_le_mul_of_nonneg_left hm1 hαr.le
  have k2 : P.αp * m2 ≤ P.αp * (x * v) := mul_le_mul_of_nonneg_left hm2 hαp.le
  have k3 : P.βr * ((x - b) * u) ≤ P.βr * M1 := mul_le_mul_of_nonneg_left hM1a (by linarith)
  have k4 : P.βr * 0 ≤ P.βr * M1 := mul_le_mul_of_nonneg_left hM1b (by linarith)
  have k5 : P.βp * ((x - a) * v) ≤ P.βp * M2 := mul_le_mul_of_nonneg_left hM2a hβp.le
  have k6 : P.βp * 0 ≤ P.βp * M2 := mul_le_mul_of_nonneg_left hM2b hβp.le
  -- key: the upper bound is ≤ target, strictly unless x = b
  have key : m1 * P.αr - M1 * P.βr + m2 * P.αp - M2 * P.βp ≤
      P.αr * (b * u) + P.αp * (b * v) - P.βp * ((b - a) * v) ∧
      (x ≠ b → m1 * P.αr - M1 * P.βr + m2 * P.αp - M2 * P.βp <
      P.αr * (b * u) + P.αp * (b * v) - P.βp * ((b - a) * v)) := by
    rcases le_or_gt x b with hxb | hxb
    · -- x ≤ b
      have strict : x < b → 0 < (b - a) * (P.αr * (u - v)) ∧ 0 < b - x ∧ v < u := by
        intro hlt
        have hspos : 0 < s := by
          by_contra h; push Not at h
          have : s = 0 := le_antisymm h hs0
          rw [hb', this] at hlt; simp at hlt; linarith
        have hba : a < b := by rw [ha, hb']; exact mul_lt_mul_of_pos_right hgpr hspos
        have huv : v < u := by
          rw [hu, hv']; exact one_div_lt_one_div_of_lt hdb (by linarith)
        exact ⟨mul_pos (by linarith) (mul_pos hαr (by linarith)), by linarith, huv⟩
      have h1 : 0 ≤ (b - x) * (P.αr * (u - v)) := mul_nonneg (by linarith) (mul_nonneg hαr.le (by linarith))
      have h2 : 0 ≤ (b - x) * v * (P.αp + P.αr - P.βp) := mul_nonneg (mul_nonneg (by linarith) hv.le) (by linarith)
      rcases le_or_gt x a with hxa | hxa
      · have h3 : 0 ≤ (a - x) * (P.βp * v) := mul_nonneg (by linarith) (by positivity)
        have h4 : 0 ≤ (b - a) * (P.αr * (u - v)) := mul_nonneg (by linarith) (mul_nonneg hαr.le (by linarith))
        have h5 : 0 ≤ (a - x) * v * (P.αp + P.αr - P.βp) := mul_nonneg (mul_nonneg (by linarith) hv.le) (by linarith)
        constructor
        · linarith
        · intro hne
          obtain ⟨hs1, -, -⟩ := strict (lt_of_le_of_ne hxb hne)
          have h6 : 0 ≤ (b - a) * v * (P.αp + P.αr - P.βp) :=
            mul_nonneg (mul_nonneg (by linarith) hv.le) (by linarith)
          have h7 : 0 ≤ (a - x) * (P.αr * u + P.αp * v) :=
            mul_nonneg (by linarith) (by positivity)
          linarith
      · constructor
        · linarith
        · intro hne
          obtain ⟨hs1, hs2, huv⟩ := strict (lt_of_le_of_ne hxb hne)
          have : 0 < (b - x) * (P.αr * (u - v)) := by
            have : 0 < P.αr * (u - v) := by
              have : 0 < u - v := by linarith
              positivity
            exact mul_pos hs2 this
          linarith
    · have h1 : 0 ≤ (x - b) * u * (P.βr - P.αr) := mul_nonneg (mul_nonneg (by linarith) (by positivity)) (by linarith)
      have h2 : 0 < (x - b) * v * (P.βp - P.αp) := mul_pos (mul_pos (by linarith) hv) (by linarith)
      have h3 : 0 ≤ (b - a) * v := mul_nonneg (by linarith) hv.le
      exact ⟨by linarith, fun _ => by linarith⟩
  have hc' : c = 1 - b ↔ x = b := by rw [hx]; constructor <;> intro h <;> linarith
  refine ⟨by linarith [key.1], ?_⟩
  rw [hc']
  constructor
  · intro heq
    by_contra hne
    have := key.2 hne
    linarith
  · intro hxb
    have q1 : m1 = b * u := by simp only [m1, hxb]; exact min_eq_left hbu
    have q2 : M1 = 0 := by simp only [M1, hxb, sub_self, zero_mul, max_self]
    have q3 : m2 = b * v := by simp only [m2, hxb]; exact min_eq_left hbv
    have q4 : M2 = (b - a) * v := by
      simp only [M2, hxb]; exact max_eq_left (mul_nonneg (by linarith) hv.le)
    rw [q1, q2, q3, q4]; ring


lemma eo_bound (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) (cp cr : ℝ) (hcp : cp ∈ Set.Icc (0 : ℝ) 1)
    (hcr : cr ∈ Set.Icc (0 : ℝ) 1) (hE : EOConstraint P cp cr s) :
    profit P k cp cr s ≤ piEO P k s ∧
    (P.γr * s / (1 - P.γr * s) < (1 - cr) / (1 - P.γr * s) → profit P k cp cr s < piEO P k s) := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  obtain ⟨hs0, ha0, hab', hb⟩ := s_bounds P hS s hs
  obtain ⟨hda, hdb, hvu, hv, hbu, hbv, hav⟩ := thr_setup P hS s hs
  have hL' : P.βp ≤ P.αp + P.αr := hL
  unfold EOConstraint at hE
  unfold profit piEO
  set τ := tau P k s
  set a := P.γp * s with ha
  set b := P.γr * s with hb'
  set u := 1 / (1 - b) with hu
  set v := 1 / (1 - a) with hv'
  set t := (1 - cr) / (1 - b) with ht
  have e2 : (1 - b - cr) / (1 - b) = t - b * u := by rw [ht, hu]; field_simp; ring
  have e4 : (1 - a - cp) / (1 - a) = t - a * v := by
    rw [hE, hv']; field_simp; ring
  have hbu' : b / (1 - b) = b * u := by rw [hu, mul_one_div]
  have hpi : P.αp * P.γr * s / (1 - b) + P.αr * P.γr * s / (1 - b) + P.βp * P.γp * s / (1 - a)
      - P.βp * P.γr * s / (1 - b) - τ =
      (P.αp + P.αr) * (b * u) - P.βp * (b * u - a * v) - τ := by
    rw [hu, hv', hb', ha]; field_simp; ring
  rw [← hE, e2, e4, hpi, hbu']
  have hm := min_le_left t 1
  have hM1a := le_max_left (t - b * u) 0
  have hM1b := le_max_right (t - b * u) 0
  have hM2a := le_max_left (t - a * v) 0
  set m := min t 1
  set M1 := max (t - b * u) 0
  set M2 := max (t - a * v) 0
  have k1 : (P.αp + P.αr) * m ≤ (P.αp + P.αr) * t := mul_le_mul_of_nonneg_left hm (by linarith)
  have k3 : P.βr * (t - b * u) ≤ P.βr * M1 := mul_le_mul_of_nonneg_left hM1a (by linarith)
  have k4 : P.βr * 0 ≤ P.βr * M1 := mul_le_mul_of_nonneg_left hM1b (by linarith)
  have k5 : P.βp * (t - a * v) ≤ P.βp * M2 := mul_le_mul_of_nonneg_left hM2a hβp.le
  constructor
  · rcases le_or_gt t (b * u) with htb | htb
    · have : 0 ≤ (b * u - t) * (P.αp + P.αr - P.βp) := mul_nonneg (by linarith) (by linarith)
      linarith
    · have : 0 ≤ (t - b * u) * (P.βr + P.βp - P.αp - P.αr) := mul_nonneg (by linarith) (by linarith)
      linarith
  · intro htb
    have : 0 < (t - b * u) * (P.βr + P.βp - P.αp - P.αr) := mul_pos (by linarith) (by linarith)
    linarith

lemma eo_red (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) :
    (1 - P.γr * s * (1 - P.γp * s) / (1 - P.γr * s)) ∈ Set.Icc (0 : ℝ) 1 ∧
    (1 - P.γr * s) ∈ Set.Icc (0 : ℝ) 1 ∧
    EOConstraint P (1 - P.γr * s * (1 - P.γp * s) / (1 - P.γr * s)) (1 - P.γr * s) s ∧
    profit P k (1 - P.γr * s * (1 - P.γp * s) / (1 - P.γr * s)) (1 - P.γr * s) s = piEO P k s ∧
    ∀ cp cr : ℝ, cp ∈ Set.Icc (0 : ℝ) 1 → cr ∈ Set.Icc (0 : ℝ) 1 → EOConstraint P cp cr s →
      profit P k cp cr s ≤ piEO P k s := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  obtain ⟨hs0, ha0, hab', hb⟩ := s_bounds P hS s hs
  obtain ⟨hda, hdb, hvu, hv, hbu, hbv, hav⟩ := thr_setup P hS s hs
  have hcp : (1 - P.γr * s * (1 - P.γp * s) / (1 - P.γr * s)) ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : 0 ≤ P.γr * s * (1 - P.γp * s) / (1 - P.γr * s) := by positivity
    have h2 : P.γr * s * (1 - P.γp * s) / (1 - P.γr * s) ≤ 1 := by
      rw [div_le_one hdb]; nlinarith
    constructor <;> linarith
  have hcr : (1 - P.γr * s) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hE : EOConstraint P (1 - P.γr * s * (1 - P.γp * s) / (1 - P.γr * s)) (1 - P.γr * s) s := by
    have : 1 - s * P.γp ≠ 0 := by rw [mul_comm]; exact hda.ne'
    have : 1 - s * P.γr ≠ 0 := by rw [mul_comm]; exact hdb.ne'
    unfold EOConstraint; field_simp; ring
  refine ⟨hcp, hcr, hE, ?_, fun cp cr h1 h2 h3 => (eo_bound P hS hL k s hs cp cr h1 h2 h3).1⟩
  unfold profit piEO
  set a := P.γp * s with ha
  set b := P.γr * s with hb'
  set u := 1 / (1 - b) with hu
  set v := 1 / (1 - a) with hv'
  have q1 : (1 - (1 - b)) / (1 - b) = b * u := by rw [hu]; field_simp; ring
  have q2 : (1 - b - (1 - b)) / (1 - b) = 0 := by ring
  have q3 : (1 - (1 - b * (1 - a) / (1 - b))) / (1 - a) = b * u := by
    rw [hu]; field_simp; ring
  have q4 : (1 - a - (1 - b * (1 - a) / (1 - b))) / (1 - a) = b * u - a * v := by
    rw [hu, hv']; field_simp; ring
  rw [q1, q2, q3, q4, min_eq_left hbu, max_self, max_eq_left (by linarith : 0 ≤ b * u - a * v)]
  rw [hu, hv', hb', ha]; field_simp; ring

/-- The difference quotient identity for `F_q`. -/
lemma F_diff (p r q x y : ℝ) (h1 : 1 - p * x ≠ 0) (h2 : 1 - p * y ≠ 0) (h3 : 1 - r * x ≠ 0)
    (h4 : 1 - r * y ≠ 0) :
    F p r q y - F p r q x = (y - x) * ((1 - r * x) * (1 - r * y) - q ^ 2 * (1 - p * x) * (1 - p * y))
      / ((1 - p * x) * (1 - p * y) * (1 - r * x) * (1 - r * y)) := by
  unfold F
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = 1 - p * x := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = 1 - p * y := ⟨_, rfl⟩
  obtain ⟨B1, hB1⟩ : ∃ B1, B1 = 1 - r * x := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B2, B2 = 1 - r * y := ⟨_, rfl⟩
  rw [← hA1] at h1; rw [← hA2] at h2; rw [← hB1] at h3; rw [← hB2] at h4
  rw [← hA1, ← hA2, ← hB1, ← hB2]
  field_simp
  subst hA1 hA2 hB1 hB2
  ring

lemma F_unimodal (p r q c : ℝ) (hp : 0 < p) (hpr : p < r) (hq0 : 0 < q) (hq1 : q < 1)
    (hc : 0 < c) (f : ℝ → ℝ)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) (1 / (2 * r)), f s = c * F p r q s)
    (hm : sstar p r q ≤ 1 / (2 * r)) :
    StrictMonoOn f (Set.Icc 0 (sstar p r q)) ∧
    StrictAntiOn f (Set.Icc (sstar p r q) (1 / (2 * r))) := by
  have hr : 0 < r := by linarith
  have hw : 0 < r - p * q := by nlinarith
  have hrs : ∀ z, z ≤ 1 / (2 * r) → r * z ≤ 1 / 2 := by
    intro z hz; rw [le_div_iff₀ (by positivity)] at hz; linarith
  -- sign facts relative to s*
  have below : ∀ z, z < sstar p r q → q * (1 - p * z) < 1 - r * z := by
    intro z hz; unfold sstar at hz; rw [lt_div_iff₀ hw] at hz; linarith
  have below' : ∀ z, z ≤ sstar p r q → q * (1 - p * z) ≤ 1 - r * z := by
    intro z hz; unfold sstar at hz; rw [le_div_iff₀ hw] at hz; linarith
  have above : ∀ z, sstar p r q < z → 1 - r * z < q * (1 - p * z) := by
    intro z hz; unfold sstar at hz; rw [div_lt_iff₀ hw] at hz; linarith
  have above' : ∀ z, sstar p r q ≤ z → 1 - r * z ≤ q * (1 - p * z) := by
    intro z hz; unfold sstar at hz; rw [div_le_iff₀ hw] at hz; linarith
  have hs0 := (sstar_mem p r q hp hpr hq1 (by
    have : r / (2 * r - p) ≤ q ∨ q < r / (2 * r - p) := le_or_gt _ _
    rcases this with h | h
    · exact h
    · exfalso
      have h2 : 0 < 2 * r - p := by linarith
      rw [lt_div_iff₀ h2] at h
      have : (1 - q) * (2 * r) ≤ r - p * q := by
        unfold sstar at hm; rw [div_le_div_iff₀ hw (by positivity)] at hm; linarith
      nlinarith)).1
  have gen : ∀ x y, 0 ≤ x → x < y → y ≤ 1 / (2 * r) →
      f y - f x = c * ((y - x) * ((1 - r * x) * (1 - r * y) - q ^ 2 * (1 - p * x) * (1 - p * y))
        / ((1 - p * x) * (1 - p * y) * (1 - r * x) * (1 - r * y))) := by
    intro x y hx hxy hy
    have hry := hrs y hy
    have hpx : p * x ≤ r * x := mul_le_mul_of_nonneg_right hpr.le hx
    have hpy : p * y ≤ r * y := mul_le_mul_of_nonneg_right hpr.le (by linarith)
    have hrx : r * x ≤ r * y := mul_le_mul_of_nonneg_left hxy.le hr.le
    rw [hf y ⟨by linarith, hy⟩, hf x ⟨hx, by linarith⟩, ← mul_sub,
      F_diff p r q x y (by linarith) (by linarith) (by linarith) (by linarith)]
  have dens : ∀ x y, 0 ≤ x → x < y → y ≤ 1 / (2 * r) →
      0 < (1 - p * x) * (1 - p * y) * (1 - r * x) * (1 - r * y) ∧
      0 < 1 - p * x ∧ 0 < 1 - p * y ∧ 0 < 1 - r * x ∧ 0 < 1 - r * y := by
    intro x y hx hxy hy
    have hry := hrs y hy
    have hpx : p * x ≤ r * x := mul_le_mul_of_nonneg_right hpr.le hx
    have hpy : p * y ≤ r * y := mul_le_mul_of_nonneg_right hpr.le (by linarith)
    have hrx : r * x ≤ r * y := mul_le_mul_of_nonneg_left hxy.le hr.le
    have a1 : 0 < 1 - p * x := by linarith
    have a2 : 0 < 1 - p * y := by linarith
    have a3 : 0 < 1 - r * x := by linarith
    have a4 : 0 < 1 - r * y := by linarith
    exact ⟨by positivity, a1, a2, a3, a4⟩
  constructor
  · intro x hx y hy hxy
    have hy' : y ≤ 1 / (2 * r) := le_trans hy.2 hm
    have hg := gen x y hx.1 hxy hy'
    obtain ⟨hD, a1, a2, a3, a4⟩ := dens x y hx.1 hxy hy'
    have b1 := below x (lt_of_lt_of_le hxy hy.2)
    have b2 := below' y hy.2
    have hN : 0 < (1 - r * x) * (1 - r * y) - q ^ 2 * (1 - p * x) * (1 - p * y) := by
      have e : (1 - r * x) * (1 - r * y) - q ^ 2 * (1 - p * x) * (1 - p * y) =
          (1 - r * x) * ((1 - r * y) - q * (1 - p * y)) +
            q * (1 - p * y) * ((1 - r * x) - q * (1 - p * x)) := by ring
      rw [e]
      have : 0 ≤ (1 - r * x) * ((1 - r * y) - q * (1 - p * y)) := mul_nonneg a3.le (by linarith)
      have : 0 < q * (1 - p * y) * ((1 - r * x) - q * (1 - p * x)) :=
        mul_pos (mul_pos hq0 a2) (by linarith)
      linarith
    have : 0 < f y - f x := by
      rw [hg]; exact mul_pos hc (div_pos (mul_pos (by linarith) hN) hD)
    linarith
  · intro x hx y hy hxy
    have hg := gen x y (le_trans hs0.le hx.1) hxy hy.2
    obtain ⟨hD, a1, a2, a3, a4⟩ := dens x y (le_trans hs0.le hx.1) hxy hy.2
    have b1 := above' x hx.1
    have b2 := above y (lt_of_le_of_lt hx.1 hxy)
    have hN : (1 - r * x) * (1 - r * y) - q ^ 2 * (1 - p * x) * (1 - p * y) < 0 := by
      have e : (1 - r * x) * (1 - r * y) - q ^ 2 * (1 - p * x) * (1 - p * y) =
          -(q * (1 - p * x) * (q * (1 - p * y) - (1 - r * y)) +
            (1 - r * y) * (q * (1 - p * x) - (1 - r * x))) := by ring
      rw [e]
      have : 0 < q * (1 - p * x) * (q * (1 - p * y) - (1 - r * y)) :=
        mul_pos (mul_pos hq0 a1) (by linarith)
      have : 0 ≤ (1 - r * y) * (q * (1 - p * x) - (1 - r * x)) := mul_nonneg a4.le (by linarith)
      linarith
    have : f y - f x < 0 := by
      rw [hg]
      apply mul_neg_of_pos_of_neg hc
      apply div_neg_of_neg_of_pos _ hD
      exact mul_neg_of_pos_of_neg (by linarith) hN
    linarith

lemma unimodal_pf (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ) :
    (∃ m₁ ∈ Set.Icc (0 : ℝ) P.sMax,
      StrictMonoOn (piET P k) (Set.Icc 0 m₁) ∧ StrictAntiOn (piET P k) (Set.Icc m₁ P.sMax)) ∧
    (∃ m₂ ∈ Set.Icc (0 : ℝ) P.sMax,
      StrictMonoOn (piEO P k) (Set.Icc 0 m₂) ∧ StrictAntiOn (piEO P k) (Set.Icc m₂ P.sMax)) := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  have hr := rho_bounds P hS
  have hσ0 : 0 < σ := by have := hC.2.1.1; linarith
  obtain ⟨hq1, hq2, -⟩ : σ < qEO P k ∧ qEO P k < 1 ∧
      P.βp * P.γp * qEO P k ^ 2 = k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr :=
    q_bounds P hS k σ hC
  rw [sMax_eq]
  obtain ⟨m1a, m1b⟩ := sstar_mem P.γp P.γr σ hgp hgpr hC.2.1.2 (sigma_ge P hS k σ hC)
  obtain ⟨m2a, m2b⟩ := sstar_mem P.γp P.γr (qEO P k) hgp hgpr hq2 (q_ge P hS k σ hC).le
  exact ⟨⟨_, ⟨m1a.le, m1b⟩, F_unimodal P.γp P.γr σ P.Acoef hgp hgpr hσ0 hC.2.1.2
      (Acoef_pos P hS k σ hC) _ (piET_on P k σ hC) m1b⟩,
    ⟨_, ⟨m2a.le, m2b⟩, F_unimodal P.γp P.γr (qEO P k) (P.βp * P.γp) hgp hgpr (by linarith) hq2
      (mul_pos hβp hgp) _ (piEO_on P hS k σ hC) m2b⟩⟩

lemma interior_pf (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ) :
    (∃ s ∈ Set.Icc (0 : ℝ) P.sMax, IsMaxOn (piET P k) (Set.Icc 0 P.sMax) s) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) P.sMax, IsMaxOn (piET P k) (Set.Icc 0 P.sMax) s →
      0 < s ∧ s ≤ P.sMax) ∧
    (∃ s ∈ Set.Icc (0 : ℝ) P.sMax, IsMaxOn (piEO P k) (Set.Icc 0 P.sMax) s) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) P.sMax, IsMaxOn (piEO P k) (Set.Icc 0 P.sMax) s →
      0 < s ∧ s < P.sMax) := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  obtain ⟨hq1, hq2, -⟩ : σ < qEO P k ∧ qEO P k < 1 ∧
      P.βp * P.γp * qEO P k ^ 2 = k - P.αr * P.γr + P.βp * P.γr - P.αp * P.γr :=
    q_bounds P hS k σ hC
  obtain ⟨m1a, m1b⟩ := sstar_mem P.γp P.γr σ hgp hgpr hC.2.1.2 (sigma_ge P hS k σ hC)
  obtain ⟨m2a, m2b⟩ := sstar_mem P.γp P.γr (qEO P k) hgp hgpr hq2 (q_ge P hS k σ hC).le
  have m2c := sstar_lt P.γp P.γr (qEO P k) hgp hgpr hq2 (q_ge P hS k σ hC)
  refine ⟨⟨_, ⟨m1a.le, m1b⟩, ?_⟩, ?_, ⟨_, ⟨m2a.le, m2b⟩, ?_⟩, ?_⟩
  · rw [sMax_eq]
    exact sstar_isMax P.γp P.γr σ P.Acoef hgp hgpr hC.2.1.2 (sigma_ge P hS k σ hC)
      (Acoef_pos P hS k σ hC) _ (piET_on P k σ hC)
  · intro s hs hmax
    rw [sET_eq P hS k σ hC s hs hmax]
    exact ⟨m1a, m1b⟩
  · rw [sMax_eq]
    exact sstar_isMax P.γp P.γr (qEO P k) (P.βp * P.γp) hgp hgpr hq2 (q_ge P hS k σ hC).le
      (mul_pos hβp hgp) _ (piEO_on P hS k σ hC)
  · intro s hs hmax
    rw [sEO_eq P hS k σ hC s hs hmax]
    exact ⟨m2a, m2c⟩

end UF2Lib

theorem solution (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k s c : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    profit P k c c s ≤ piET P k s ∧ (profit P k c c s = piET P k s ↔ c = 1 - P.γr * s) :=
  UF2Lib.et_red P hS hL k s c hs hc
