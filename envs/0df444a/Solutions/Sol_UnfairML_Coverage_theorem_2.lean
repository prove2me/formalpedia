-- Prove2me | solution 1 for UnfairML.Coverage.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T05:56:17.225498+00:00
-- url     : https://prove2.me/submissions/62fe6de0-ac48-4545-ba1b-9e27e3a27539

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model
import Theorems.Thm_UnfairML_Coverage_et_threshold_reduction
import Theorems.Thm_UnfairML_Coverage_eo_threshold_reduction
import Theorems.Thm_UnfairML_Coverage_eq_51
import Theorems.Thm_UnfairML_Coverage_eq_52
import Theorems.Thm_UnfairML_Coverage_eq_54
import Theorems.Thm_UnfairML_Coverage_eq_59

open UnfairML.Coverage

namespace UF2Red

lemma facts (P : Params) (hS : P.Standing) :
    0 < P.αp ∧ 0 < P.βp ∧ 0 < P.αr ∧ P.αr ≤ P.βr ∧ P.αp < P.βp ∧ 0 < P.γp ∧ P.γp < P.γr ∧
    0 < P.γr := by
  obtain ⟨hα, hβ, hdr, hdrp, hdp, hab, hgp, hgpr⟩ := hS
  simp only [Params.αp, Params.βp, Params.αr, Params.βr] at *
  refine ⟨mul_pos hα (by linarith), mul_pos hβ (by linarith), mul_pos hα (by linarith), hab,
    ?_, hgp, hgpr, by linarith⟩
  have : (P.α + P.β) * (P.dp - P.dr) > 0 := mul_pos (by linarith) (by linarith)
  nlinarith

lemma s_bounds (P : Params) (hS : P.Standing) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) :
    0 ≤ s ∧ 0 ≤ P.γp * s ∧ P.γp * s ≤ P.γr * s ∧ P.γr * s ≤ 1 / 2 := by
  obtain ⟨-, -, -, -, -, hgp, hgpr, hgr⟩ := facts P hS
  obtain ⟨h0, h1⟩ := hs
  unfold Params.sMax at h1
  have : P.γr * s ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  exact ⟨h0, by positivity, by nlinarith, this⟩

/-- Under (6), raising the common coverage rate above `γr s/(1 − γr s)` strictly lowers profit. -/
lemma eo_strict (P : Params) (hS : P.Standing) (k s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) P.sMax) (cp cr : ℝ) (hE : EOConstraint P cp cr s)
    (htb : P.γr * s / (1 - P.γr * s) < (1 - cr) / (1 - P.γr * s)) :
    profit P k cp cr s < piEO P k s := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := facts P hS
  obtain ⟨hs0, ha0, hab', hb⟩ := s_bounds P hS s hs
  have hda : 0 < 1 - P.γp * s := by linarith
  have hdb : 0 < 1 - P.γr * s := by linarith
  unfold EOConstraint at hE
  unfold profit piEO
  set τ := tau P k s
  set a := P.γp * s with ha
  set b := P.γr * s with hb'
  set u := 1 / (1 - b) with hu
  set v := 1 / (1 - a) with hv'
  have hv : 0 < v := by positivity
  set t := (1 - cr) / (1 - b) with ht
  have e2 : (1 - b - cr) / (1 - b) = t - b * u := by rw [ht, hu]; field_simp; ring
  have e4 : (1 - a - cp) / (1 - a) = t - a * v := by
    rw [hE, hv']; field_simp; ring
  have hbu' : b / (1 - b) = b * u := by rw [hu, mul_one_div]
  have hpi : P.αp * P.γr * s / (1 - b) + P.αr * P.γr * s / (1 - b) + P.βp * P.γp * s / (1 - a)
      - P.βp * P.γr * s / (1 - b) - τ =
      (P.αp + P.αr) * (b * u) - P.βp * (b * u - a * v) - τ := by
    rw [hu, hv', hb', ha]; field_simp; ring
  rw [← hE, e2, e4, hpi]
  rw [hbu'] at htb
  have hm := min_le_left t 1
  have hM1a := le_max_left (t - b * u) 0
  have hM2a := le_max_left (t - a * v) 0
  set m := min t 1
  set M1 := max (t - b * u) 0
  set M2 := max (t - a * v) 0
  have k1 : (P.αp + P.αr) * m ≤ (P.αp + P.αr) * t := mul_le_mul_of_nonneg_left hm (by linarith)
  have k3 : P.βr * (t - b * u) ≤ P.βr * M1 := mul_le_mul_of_nonneg_left hM1a (by linarith)
  have k5 : P.βp * (t - a * v) ≤ P.βp * M2 := mul_le_mul_of_nonneg_left hM2a hβp.le
  have : 0 < (t - b * u) * (P.βr + P.βp - P.αp - P.αr) := mul_pos (by linarith) (by linarith)
  linarith

end UF2Red

theorem solution (P : Params) (hS : P.Standing) (hL : P.LowLoss) (k σ : ℝ)
    (hC : CostRange P k σ)
    (hcond : P.αp / P.βp ≤
      1 - (1 - (2 - σ) ^ 2 * σ ^ 2) / ((1 - σ ^ 2) * (2 - σ) ^ 2) * (P.γp / P.γr))
    (cET sET : ℝ) (hET : IsOptET P k cET sET)
    (cpEO crEO sEO : ℝ) (hEO : IsOptEO P k cpEO crEO sEO) :
    coverage P.γp cpEO sEO ≤ coverage P.γp cET sET := by
  obtain ⟨hαp, hβp, hαr, hab, hgap, hgp, hgpr, hgr⟩ := UF2Red.facts P hS
  -- Equal treatment: the optimal effort maximizes πET and the threshold is 1 − γr s.
  obtain ⟨hc, hs, hoptET⟩ := hET
  have hETfeas : ∀ s' ∈ Set.Icc (0 : ℝ) P.sMax,
      piET P k s' = profit P k (1 - P.γr * s') (1 - P.γr * s') s' := by
    intro s' hs'
    obtain ⟨-, -, hb⟩ := UF2Red.s_bounds P hS s' hs'
    have hc' : (1 - P.γr * s') ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by nlinarith⟩
    exact ((et_threshold_reduction P hS hL k s' _ hs' hc').2.2 rfl).symm
  have hmaxET : IsMaxOn (piET P k) (Set.Icc 0 P.sMax) sET := by
    intro s' hs'
    show piET P k s' ≤ piET P k sET
    obtain ⟨-, -, hb⟩ := UF2Red.s_bounds P hS s' hs'
    have hc' : (1 - P.γr * s') ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by nlinarith⟩
    rw [hETfeas s' hs']
    exact le_trans (hoptET _ _ hc' hs') (et_threshold_reduction P hS hL k sET cET hs hc).1
  have hcET : cET = 1 - P.γr * sET := by
    apply ((et_threshold_reduction P hS hL k sET cET hs hc).2).1
    apply le_antisymm (et_threshold_reduction P hS hL k sET cET hs hc).1
    obtain ⟨-, -, hb⟩ := UF2Red.s_bounds P hS sET hs
    have hc' : (1 - P.γr * sET) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by nlinarith⟩
    rw [hETfeas sET hs]
    exact hoptET _ _ hc' hs
  have hcovET : coverage P.γp cET sET = P.γr * sET / (1 - P.γp * sET) := by
    obtain ⟨hs0, ha0, hab', hb⟩ := UF2Red.s_bounds P hS sET hs
    have hda : 0 < 1 - P.γp * sET := by linarith
    unfold coverage
    rw [hcET, show 1 - (1 - P.γr * sET) = P.γr * sET by ring]
    apply min_eq_left
    rw [div_le_one hda]; linarith
  -- Equal opportunity: the optimal effort maximizes πEO, and the coverage rate is at most
  -- γr s/(1 − γr s).
  obtain ⟨hcp, hcr, hs2, hE, hoptEO⟩ := hEO
  have hEOfeas : ∀ s' ∈ Set.Icc (0 : ℝ) P.sMax, piEO P k s' ≤ profit P k cpEO crEO sEO := by
    intro s' hs'
    obtain ⟨h1, h2, h3, h4, -⟩ := eo_threshold_reduction P hS hL k s' hs'
    rw [← h4]
    exact hoptEO _ _ _ h1 h2 hs' h3
  have hmaxEO : IsMaxOn (piEO P k) (Set.Icc 0 P.sMax) sEO := by
    intro s' hs'
    show piEO P k s' ≤ piEO P k sEO
    exact le_trans (hEOfeas s' hs')
      ((eo_threshold_reduction P hS hL k sEO hs2).2.2.2.2 cpEO crEO hcp hcr hE)
  have ht : (1 - crEO) / (1 - P.γr * sEO) ≤ P.γr * sEO / (1 - P.γr * sEO) := by
    by_contra h
    push Not at h
    have := UF2Red.eo_strict P hS k sEO hs2 cpEO crEO hE h
    have := hEOfeas sEO hs2
    linarith
  have hcovEO : coverage P.γp cpEO sEO ≤ P.γr * sEO / (1 - P.γr * sEO) := by
    unfold coverage
    unfold EOConstraint at hE
    rw [← hE]
    exact le_trans (min_le_left _ _) ht
  -- Closed forms (51), (52), the difference (54), and the sign (59).
  have h51 := eq_51 P hS hL k σ hC sET hs hmaxET
  have h52 := eq_52 P hS hL k σ hC sEO hs2 hmaxEO
  have h54 := eq_54 P hS hL k σ hC
  have h59 := eq_59 P hS hL σ hC.2.1 hcond
  have hpre : 0 < P.γr / (P.γr - P.γp) := div_pos hgr (by linarith)
  have hdiff : 0 ≤ P.γr / (P.γr - P.γp) *
      (2 - σ - Real.sqrt (P.βp * P.γp /
        (σ ^ 2 * P.βp * P.γp + (1 - σ ^ 2) * (P.βp * P.γr - P.αp * P.γr)))) :=
    mul_nonneg hpre.le (by linarith)
  rw [hcovET, h51]
  rw [h52] at hcovEO
  linarith
