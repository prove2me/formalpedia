-- Prove2me | solution 1 for PlatformToken.SmallCost.eq_B29_right
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:27:48.595823+00:00
-- url     : https://prove2.me/submissions/e888fe08-4c99-492e-9ba5-02242da55edb

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting
import Definitions.Def_PlatformToken_SmallCost_Corollary1

set_option autoImplicit false
open PlatformToken.SmallCost

theorem solution(p : Params) (hp : p.Standing) (hK : 0 < p.K) (Q e : ℝ) (hQ : 0 < Q)
    (he : 0 < e) (hh : h p e Q = 0) :
    e < estar p Q := by
  have ha := hp.a_pos
  have hab := hp.a_lt_b
  have hb1 := hp.b_lt_one
  have hδ := hp.δ_pos
  have hδ1 := hp.δ_lt_one
  have hγ := hp.γ_pos
  have hD : 0 < d p e Q * Q := mul_pos (mul_pos (Real.rpow_pos_of_pos he _) (Real.rpow_pos_of_pos hQ _)) hQ
  have hCc : 0 < Ccap p Q := mul_pos hK (Real.rpow_pos_of_pos hQ _)
  have hFe : 0 < Fe p e Q := mul_pos (mul_pos ha (Real.rpow_pos_of_pos he _)) (Real.rpow_pos_of_pos hQ _)
  have h1δ : 0 < 1 - p.δ := by linarith
  have hβ : 1 - (1 - p.δ) * Ccap p Q / (d p e Q * Q) < 1 := by
    have : 0 < (1 - p.δ) * Ccap p Q / (d p e Q * Q) := div_pos (mul_pos h1δ hCc) hD
    linarith
  unfold h at hh
  have hX : 0 < Fe p e Q / (1 - p.δ) := div_pos hFe h1δ
  have hγlt : p.γ < Fe p e Q / (1 - p.δ) := by
    have : (1 - (1 - p.δ) * Ccap p Q / (d p e Q * Q)) * Fe p e Q / (1 - p.δ) = (1 - (1 - p.δ) * Ccap p Q / (d p e Q * Q)) * (Fe p e Q / (1 - p.δ)) := by ring
    nlinarith [mul_lt_mul_of_pos_right hβ hX]
  have hfe : (1 - p.δ) * p.γ < p.a * e ^ (p.a - 1) * Q ^ (1 - p.b) := by
    rw [lt_div_iff₀ h1δ] at hγlt; unfold Fe at hγlt; linarith
  have hQb : 0 < Q ^ (1 - p.b) := Real.rpow_pos_of_pos hQ _
  have hea : 0 < e ^ (p.a - 1) := Real.rpow_pos_of_pos he _
  have hlt : e ^ (1 - p.a) < p.a * Q ^ (1 - p.b) / ((1 - p.δ) * p.γ) := by
    have h1 : e ^ (1 - p.a) = (e ^ (p.a - 1))⁻¹ := by
      rw [← Real.rpow_neg he.le]; congr 1; ring
    rw [h1, lt_div_iff₀ (mul_pos h1δ hγ)]
    rw [inv_mul_eq_div, div_lt_iff₀ hea]
    linarith
  have hpos : 0 < 1 / (1 - p.a) := by apply div_pos one_pos; linarith
  have he' : e = (e ^ (1 - p.a)) ^ (1 / (1 - p.a)) := by
    rw [one_div, Real.rpow_rpow_inv he.le (by linarith)]
  unfold estar
  calc e = (e ^ (1 - p.a)) ^ (1 / (1 - p.a)) := he'
    _ < _ := Real.rpow_lt_rpow (Real.rpow_nonneg he.le _) hlt hpos
