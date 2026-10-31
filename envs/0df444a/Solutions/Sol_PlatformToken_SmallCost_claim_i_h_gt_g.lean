-- Prove2me | solution 1 for PlatformToken.SmallCost.claim_i_h_gt_g
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:27:50.978252+00:00
-- url     : https://prove2.me/submissions/9148892b-48ea-4fc0-bac6-e03d53b8723f

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting
import Definitions.Def_PlatformToken_SmallCost_Corollary1

set_option autoImplicit false
open PlatformToken.SmallCost

theorem solution(p : Params) (hp : p.Standing) (hcm : 0 < p.c ∨ 0 < p.m)
    (hK : 0 < p.K) (Q e : ℝ) (hQ : 0 < Q) (he : 0 < e) (hsd : s p Q < d p e Q) :
    g p e Q < h p e Q := by
  have ha := hp.a_pos
  have hδ := hp.δ_pos
  have hδ1 := hp.δ_lt_one
  have hm := hp.m_nonneg
  have hc := hp.c_nonneg
  have h1δ : 0 < 1 - p.δ := by linarith
  have hdp : 0 < d p e Q := mul_pos (Real.rpow_pos_of_pos he _) (Real.rpow_pos_of_pos hQ _)
  have hs0 : 0 ≤ s p Q := mul_nonneg hm (Real.rpow_nonneg hQ.le _)
  have hCc : 0 < Ccap p Q := mul_pos hK (Real.rpow_pos_of_pos hQ _)
  have hFe : 0 < Fe p e Q := mul_pos (mul_pos ha (Real.rpow_pos_of_pos he _)) (Real.rpow_pos_of_pos hQ _)
  have hX : 0 < Fe p e Q / (1 - p.δ) := div_pos hFe h1δ
  have hcm' : 0 < s p Q + (1 - p.δ) * p.c := by
    rcases hcm with h | h
    · nlinarith
    · have : 0 < s p Q := mul_pos h (Real.rpow_pos_of_pos hQ _)
      nlinarith
  have e1 : ∀ x : ℝ, x * Fe p e Q / (1 - p.δ) = x * (Fe p e Q / (1 - p.δ)) := fun x => by ring
  unfold g h
  split_ifs with hcd
  · have hden : 0 < d p e Q * Q - s p Q * Q - (1 - p.δ) * p.c * Q := by
      have : 0 < d p e Q - s p Q - (1 - p.δ) * p.c := by nlinarith
      nlinarith
    have hlt : (1 - p.δ) * Ccap p Q / (d p e Q * Q) < (1 - p.δ) * Ccap p Q / (d p e Q * Q - s p Q * Q - (1 - p.δ) * p.c * Q) := by
      apply div_lt_div_of_pos_left (mul_pos h1δ hCc) hden
      nlinarith
    have := mul_lt_mul_of_pos_right (by linarith : 1 - (1 - p.δ) * Ccap p Q / (d p e Q * Q - s p Q * Q - (1 - p.δ) * p.c * Q) < 1 - (1 - p.δ) * Ccap p Q / (d p e Q * Q)) hX
    rw [e1, e1]
    linarith
  · push Not at hcd
    have hA : 0 < d p e Q * Q := mul_pos hdp hQ
    have hAS : 0 < d p e Q * Q - s p Q * Q := by nlinarith
    have hden : 0 < p.δ * (d p e Q * Q - s p Q * Q) := mul_pos hδ hAS
    have hdenlt : p.δ * (d p e Q * Q - s p Q * Q) < d p e Q * Q := by nlinarith [mul_nonneg hs0 hQ.le]
    have hN : Ccap p Q < Ccap p Q + p.c * Q - d p e Q * Q + s p Q * Q := by nlinarith
    have hlt : (1 - p.δ) * Ccap p Q / (d p e Q * Q) < (1 - p.δ) * (Ccap p Q + p.c * Q - d p e Q * Q + s p Q * Q) / (p.δ * (d p e Q * Q - s p Q * Q)) := by
      rw [div_lt_div_iff₀ hA hden]
      have := mul_lt_mul_of_pos_left hN h1δ
      have h2 : (1 - p.δ) * Ccap p Q * (p.δ * (d p e Q * Q - s p Q * Q)) < (1 - p.δ) * Ccap p Q * (d p e Q * Q) := mul_lt_mul_of_pos_left hdenlt (mul_pos h1δ hCc)
      nlinarith [mul_lt_mul_of_pos_right this hden]
    have := mul_lt_mul_of_pos_right (by linarith : 1 - (1 - p.δ) * (Ccap p Q + p.c * Q - d p e Q * Q + s p Q * Q) / (p.δ * (d p e Q * Q - s p Q * Q)) < 1 - (1 - p.δ) * Ccap p Q / (d p e Q * Q)) hX
    rw [e1, e1]
    linarith
