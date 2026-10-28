-- Prove2me | solution 1 for TsayQF.EffQF.system_profit_eq_cc
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:02:55.853047+00:00
-- url     : https://prove2.me/submissions/2a9156a9-9dd7-4764-98ed-9c0c0eb0257e

import Mathlib
import Definitions.Def_TsayQF_EffQF_Model

open MeasureTheory ProbabilityTheory

namespace Aux_TQFsp
open TsayQF.EffQF

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

lemma int_posA (hid : Integrable id ν) (a : ℝ) : Integrable (fun μ : ℝ => max (μ - a) 0) ν :=
  (hid.sub (integrable_const a)).pos_part

lemma int_posB (hid : Integrable id ν) (a : ℝ) : Integrable (fun μ : ℝ => max (a - μ) 0) ν :=
  ((integrable_const a).sub hid).pos_part

lemma int_min (hid : Integrable id ν) (a : ℝ) : Integrable (fun μ : ℝ => min μ a) ν := by
  have h : (fun μ : ℝ => min μ a) = fun μ => id μ - max (μ - a) 0 := by
    funext μ; simp only [id]
    rcases le_total μ a with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  rw [h]; exact hid.sub (int_posA hid a)

lemma int_clip (hid : Integrable id ν) (lo Q : ℝ) :
    Integrable (fun μ : ℝ => clip μ lo Q) ν := by
  have h : (fun μ : ℝ => clip μ lo Q) = fun μ => lo + max (min μ Q - lo) 0 := by
    funext μ; simp only [clip]
    rcases le_total (min μ Q) lo with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  rw [h]
  exact (integrable_const lo).add (((int_min hid Q).sub (integrable_const lo)).pos_part)

lemma int_h (hid : Integrable id ν) (p s u Q : ℝ) :
    Integrable (fun μ : ℝ => p * min μ Q - s * max (μ - Q) 0 + u * max (Q - μ) 0) ν :=
  (((int_min hid Q).const_mul p).sub ((int_posA hid Q).const_mul s)).add
    ((int_posB hid Q).const_mul u)

end Aux_TQFsp

open TsayQF.EffQF Aux_TQFsp in
theorem solution (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (c α ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hα : -ω ≤ α) (q : ℝ) (hq : 0 ≤ q)
    (Qcc : ℝ) (hQcc : cdf ν Qcc = kS D) :
    forecastProfit D ν c α ω q + emProfit D ν c ω q (q * (1 + α)) =
        ccProfit D ν (q * (1 + α)) ∧
      (q * (1 + α) = Qcc → ∀ Q, ccProfit D ν Q ≤
        forecastProfit D ν c α ω q + emProfit D ν c ω q (q * (1 + α))) := by
  have hid : Integrable id ν := hν.integrable (by norm_num)
  set lo := q * (1 - ω) with hlo
  set Q0 := q * (1 + α) with hQ0
  have hloQ : lo ≤ Q0 := by rw [hlo, hQ0]; nlinarith
  have part1 : forecastProfit D ν c α ω q + emProfit D ν c ω q Q0 = ccProfit D ν Q0 := by
    have hpt : ∀ μ : ℝ, G D c (clip μ lo Q0) μ =
        (D.p * min μ Q0 - D.s * max (μ - Q0) 0 + D.u * max (Q0 - μ) 0) - D.u * Q0 -
          (c - D.u) * clip μ lo Q0 := by
      intro μ
      simp only [G, clip]
      rcases le_total μ lo with h1 | h1
      · have h2 : μ ≤ Q0 := h1.trans hloQ
        have e1 : min μ Q0 = μ := min_eq_left h2
        have e2 : max lo μ = lo := max_eq_left h1
        have e3 : min μ lo = μ := min_eq_left h1
        have e4 : max (μ - lo) 0 = 0 := max_eq_right (by linarith)
        have e5 : max (lo - μ) 0 = lo - μ := max_eq_left (by linarith)
        have e6 : max (μ - Q0) 0 = 0 := max_eq_right (by linarith)
        have e7 : max (Q0 - μ) 0 = Q0 - μ := max_eq_left (by linarith)
        simp only [e1, e2, e3, e4, e5, e6, e7]
        ring
      · rcases le_total μ Q0 with h2 | h2
        · have e1 : min μ Q0 = μ := min_eq_left h2
          have e2 : max lo μ = μ := max_eq_right h1
          have e6 : max (μ - Q0) 0 = 0 := max_eq_right (by linarith)
          have e7 : max (Q0 - μ) 0 = Q0 - μ := max_eq_left (by linarith)
          simp only [e1, e2, min_self, sub_self, max_self, e6, e7]
          ring
        · have e1 : min μ Q0 = Q0 := min_eq_right h2
          have e2 : max lo Q0 = Q0 := max_eq_right hloQ
          have e6 : max (μ - Q0) 0 = μ - Q0 := max_eq_left (by linarith)
          have e7 : max (Q0 - μ) 0 = 0 := max_eq_right (by linarith)
          simp only [e1, e2, e6, e7]
          ring
    unfold forecastProfit retailerProfit emProfit ccProfit
    rw [← hQ0, ← hlo]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have i1 : Integrable (fun μ : ℝ => D.p * min μ Q0 - D.s * max (μ - Q0) 0 +
        D.u * max (Q0 - μ) 0 - D.u * Q0) ν := (int_h hid _ _ _ _).sub (integrable_const _)
    have i2 : Integrable (fun μ : ℝ => (c - D.u) * clip μ lo Q0) ν :=
      (int_clip hid lo Q0).const_mul _
    have i3 : Integrable (fun μ : ℝ => D.p * min μ Q0 - D.s * max (μ - Q0) 0 +
        D.u * max (Q0 - μ) 0) ν := int_h hid _ _ _ _
    rw [integral_sub i1 i2, integral_sub i3 (integrable_const _),
      integral_const_mul (c - D.u), integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  refine ⟨part1, ?_⟩
  intro hQeq Q
  rw [part1, hQeq]
  -- newsvendor optimality of Qcc
  have hpsu : 0 < D.p + D.s - D.u := by linarith [D.hmp, D.hum, D.hs]
  have hkS : (D.p + D.s - D.u) * (1 - kS D) = D.m - D.u := by
    unfold kS
    have hne : D.p + D.s - D.u ≠ 0 := hpsu.ne'
    first | (field_simp; ring) | field_simp
  set k := D.p + D.s - D.u with hk
  have hpt : ∀ μ : ℝ,
      (D.p * min μ Q - D.s * max (μ - Q) 0 + D.u * max (Q - μ) 0) -
        (D.p * min μ Qcc - D.s * max (μ - Qcc) 0 + D.u * max (Qcc - μ) 0) =
      k * (min μ Q - min μ Qcc) + D.u * (Q - Qcc) := by
    intro μ
    have e : ∀ a : ℝ, D.p * min μ a - D.s * max (μ - a) 0 + D.u * max (a - μ) 0 =
        k * min μ a - D.s * μ + D.u * a := by
      intro a
      rw [hk]
      rcases le_total μ a with h | h
      · rw [min_eq_left h, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    rw [e Q, e Qcc]; ring
  have hind : ∀ μ : ℝ, min μ Q - min μ Qcc ≤
      (Set.Ioi Qcc).indicator (fun _ => Q - Qcc) μ := by
    intro μ
    by_cases hμ : μ ∈ Set.Ioi Qcc
    · rw [Set.indicator_of_mem hμ]
      have hμ' : Qcc < μ := hμ
      rw [min_eq_right hμ'.le]
      have := min_le_right μ Q
      linarith
    · rw [Set.indicator_of_notMem hμ]
      have hμ' : μ ≤ Qcc := not_lt.1 hμ
      rw [min_eq_left hμ']
      have := min_le_left μ Q
      linarith
  have hint_diff : Integrable (fun μ : ℝ => min μ Q - min μ Qcc) ν :=
    (int_min hid Q).sub (int_min hid Qcc)
  have hbound : ∫ μ, (min μ Q - min μ Qcc) ∂ν ≤ (Q - Qcc) * (1 - kS D) := by
    calc ∫ μ, (min μ Q - min μ Qcc) ∂ν
        ≤ ∫ μ, (Set.Ioi Qcc).indicator (fun _ => Q - Qcc) μ ∂ν :=
          integral_mono hint_diff ((integrable_const _).indicator measurableSet_Ioi) hind
      _ = (Q - Qcc) * (1 - kS D) := by
          rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, ← Set.compl_Iic,
            probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, hQcc]
          ring
  have hdiff : ccProfit D ν Q - ccProfit D ν Qcc =
      k * ∫ μ, (min μ Q - min μ Qcc) ∂ν + D.u * (Q - Qcc) - D.m * (Q - Qcc) := by
    unfold ccProfit
    have := integral_sub (int_h hid D.p D.s D.u Q) (int_h hid D.p D.s D.u Qcc)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at this
    rw [integral_add (hint_diff.const_mul k) (integrable_const _), integral_const_mul,
      integral_const] at this
    simp only [probReal_univ, smul_eq_mul, one_mul] at this
    linarith
  have : k * ∫ μ, (min μ Q - min μ Qcc) ∂ν ≤ k * ((Q - Qcc) * (1 - kS D)) :=
    mul_le_mul_of_nonneg_left hbound hpsu.le
  have e2 : k * ((Q - Qcc) * (1 - kS D)) = (D.m - D.u) * (Q - Qcc) := by
    rw [← hkS]; ring
  linarith
