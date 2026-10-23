-- Prove2me | solution 1 for YieldPostpone.Pricing.theta_threshold
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:23:09.672572+00:00
-- url     : https://prove2.me/submissions/f1d9d309-4759-4df0-b0b7-aaaf933bbd6e

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting

open YieldPostpone.Pricing

namespace YP5TT

/-- Core inequality behind `c^OA_1 > C̃` (App. C): with `s = √μ`, `r = √(α²(1-θ)+θ)` and
`(3+4α)s < α + 2T`, `T = √(α(3+5α+α²))`, the combination `K` is positive. -/
lemma key (α θ s r T : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = α * (1 - θ) + θ) (hr0 : 0 ≤ r)
    (hr2 : r ^ 2 = α ^ 2 * (1 - θ) + θ) (hT0 : 0 ≤ T) (hT2 : T ^ 2 = α * (3 + 5 * α + α ^ 2))
    (hlt : (3 + 4 * α) * s < α + 2 * T) :
    0 < (α * (1 - θ) + θ - α * θ - 2 * θ * s) * (1 + α) - (1 - r) * (α + θ) := by
  have hsα : α < s := by
    by_contra h
    push Not at h
    have : s ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ hs0 h 2
    nlinarith
  have hs2α : 0 < s ^ 2 - α := by rw [hs2]; nlinarith
  -- g(s) < 0
  have hA : 0 < (3 + 4 * α) * s - α := by nlinarith
  have hB : (3 + 4 * α) * s - α < 2 * T := by linarith
  have hsq : ((3 + 4 * α) * s - α) ^ 2 < (2 * T) ^ 2 := pow_lt_pow_left₀ hB hA.le two_ne_zero
  have hg : (3 + 4 * α) * s ^ 2 - 2 * α * s - α ^ 2 - 4 * α < 0 := by
    have h34 : 0 < 3 + 4 * α := by linarith
    have e : (3 + 4 * α) * ((3 + 4 * α) * s ^ 2 - 2 * α * s - α ^ 2 - 4 * α) =
        ((3 + 4 * α) * s - α) ^ 2 - (2 * T) ^ 2 := by
      rw [mul_pow, hT2]; ring
    have : (3 + 4 * α) * ((3 + 4 * α) * s ^ 2 - 2 * α * s - α ^ 2 - 4 * α) < 0 := by
      rw [e]; linarith
    by_contra h
    push Not at h
    have := mul_nonneg h34.le h
    linarith
  -- the polynomial Q > 0
  set R := 2 * (1 + α) * s * (s ^ 2 - α) - α * (2 * α + α ^ 2 - (1 + 2 * α) * s ^ 2) with hR
  have hr2' : r ^ 2 = (1 + α) * s ^ 2 - α := by rw [hr2, hs2]; ring
  have hQ : R ^ 2 < (s ^ 2 - α ^ 2) ^ 2 * r ^ 2 := by
    have e : (s ^ 2 - α ^ 2) ^ 2 * ((1 + α) * s ^ 2 - α) - R ^ 2 =
        (s ^ 2 - α) * (1 + α) * (α + s) ^ 2 *
          (-((3 + 4 * α) * s ^ 2 - 2 * α * s - α ^ 2 - 4 * α)) := by
      rw [hR]; ring
    have : 0 < (s ^ 2 - α) * (1 + α) * (α + s) ^ 2 *
        (-((3 + 4 * α) * s ^ 2 - 2 * α * s - α ^ 2 - 4 * α)) := by
      apply mul_pos (mul_pos (mul_pos hs2α (by linarith)) (by positivity)) (by linarith)
    rw [hr2']; linarith
  have hsα2 : 0 < s ^ 2 - α ^ 2 := by nlinarith
  have hH : R < (s ^ 2 - α ^ 2) * r := by
    by_cases hR0 : R ≤ 0
    · have hr : 0 < r := by
        rcases hr0.lt_or_eq with h | h
        · exact h
        · rw [← h] at hr2; nlinarith
      have := mul_pos hsα2 hr
      linarith
    · push Not at hR0
      have h1 : 0 ≤ (s ^ 2 - α ^ 2) * r := mul_nonneg hsα2.le hr0
      have h2 : R ^ 2 < ((s ^ 2 - α ^ 2) * r) ^ 2 := by rw [mul_pow]; exact hQ
      exact lt_of_pow_lt_pow_left₀ 2 h1 h2
  -- (1 - α) K = H
  have hK : (1 - α) * ((α * (1 - θ) + θ - α * θ - 2 * θ * s) * (1 + α) - (1 - r) * (α + θ)) =
      (s ^ 2 - α ^ 2) * r - R := by
    have hθ' : θ * (1 - α) = s ^ 2 - α := by rw [hs2]; ring
    rw [hR]
    linear_combination (-2 * α ^ 2 - 2 * α * s - α + r - 2 * s) * hθ'
  have hpos : 0 < (1 - α) * ((α * (1 - θ) + θ - α * θ - 2 * θ * s) * (1 + α) - (1 - r) * (α + θ)) := by
    rw [hK]; linarith
  by_contra h
  push Not at h
  have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 1 - α) h
  linarith

end YP5TT

theorem solution (P : Params) (hP : P.Valid) :
    (P.θ < Theta P.α → cOA1 P > Ctil P ∧ Ctil P > 0) ∧ cOR P < Ctil P := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  set α := P.α with hα
  set θ := P.θ with hθ
  have hu : 0 < 1 - θ := by linarith
  have hμ0 : 0 < α * (1 - θ) + θ := by positivity
  have hD0 : 0 < α ^ 2 * (1 - θ) + θ := by positivity
  have hD1 : α ^ 2 * (1 - θ) + θ < 1 := by
    have h1 : α ^ 2 < 1 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right h1 hu]
  set s := Real.sqrt (α * (1 - θ) + θ) with hs
  set r := Real.sqrt (α ^ 2 * (1 - θ) + θ) with hr
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = α * (1 - θ) + θ := Real.sq_sqrt hμ0.le
  have hr2 : r ^ 2 = α ^ 2 * (1 - θ) + θ := Real.sq_sqrt hD0.le
  have hrpos : 0 < r := Real.sqrt_pos.mpr hD0
  have hr1 : r < 1 := by
    rw [hr, Real.sqrt_lt' one_pos]; simpa using hD1
  have hCtil : Ctil P > 0 := by
    unfold Ctil
    rw [← hα, ← hθ, ← hr]
    apply div_pos
    · apply mul_pos (mul_pos ha hα0); linarith
    · positivity
  refine ⟨fun hΘ => ⟨?_, hCtil⟩, ?_⟩
  · -- c^OA_1 > C̃
    set T := Real.sqrt (α * (3 + 5 * α + α ^ 2)) with hT
    have hT0 : 0 ≤ T := Real.sqrt_nonneg _
    have hT2 : T ^ 2 = α * (3 + 5 * α + α ^ 2) := Real.sq_sqrt (by positivity)
    have h34 : 0 < 3 + 4 * α := by linarith
    have hden : 0 < (1 - α) * (3 + 4 * α) ^ 2 := by
      have : 0 < 1 - α := by linarith
      positivity
    have hΘ' : θ * ((1 - α) * (3 + 4 * α) ^ 2) < α * (3 * (1 - α - 4 * α ^ 2) + 4 * T) := by
      have := hΘ
      unfold Theta at this
      rw [lt_div_iff₀ hden] at this
      rw [hT]; exact this
    have hlt2 : ((3 + 4 * α) * s) ^ 2 < (α + 2 * T) ^ 2 := by
      rw [mul_pow, hs2]; nlinarith
    have hlt : (3 + 4 * α) * s < α + 2 * T :=
      lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt2
    have hK := YP5TT.key α θ s r T hα0 hα1 hθ0 hθ1 hs0 hs2 hr0 hr2 hT0 hT2 hlt
    have hμ : μ P = α * (1 - θ) + θ := rfl
    have e : cOA1 P - Ctil P = P.a * α *
        ((α * (1 - θ) + θ - α * θ - 2 * θ * s) * (1 + α) - (1 - r) * (α + θ)) /
          (P.b * (α + θ) * (1 + α)) := by
      unfold cOA1 Ctil
      rw [hμ, ← hα, ← hθ, ← hs, ← hr]
      field_simp
      try ring
    have : 0 < cOA1 P - Ctil P := by
      rw [e]; apply div_pos (mul_pos (mul_pos ha hα0) hK); positivity
    linarith
  · -- c^OR < C̃
    set v := Real.sqrt (α ^ 2 + θ / (1 - θ)) with hv
    have hv0 : 0 ≤ v := Real.sqrt_nonneg _
    have hv2 : v ^ 2 = α ^ 2 + θ / (1 - θ) := Real.sq_sqrt (by positivity)
    have huv2 : ((1 - θ) * v) ^ 2 = (1 - θ) * r ^ 2 := by
      rw [mul_pow, hv2, hr2]; field_simp; try ring
    -- (1 - r)^2 < (1+α)^2 (1-θ)
    have h1r : (1 - r) * (1 + r) = (1 - θ) * (1 - α) * (1 + α) := by
      have : (1 - r) * (1 + r) = 1 - r ^ 2 := by ring
      rw [this, hr2]; ring
    have hk : (1 - r) ^ 2 < (1 + α) ^ 2 * (1 - θ) := by
      have e2 : ((1 - r) * (1 + r)) ^ 2 = (1 - θ) ^ 2 * (1 - α) ^ 2 * (1 + α) ^ 2 := by
        rw [h1r]; ring
      have hlt : (1 - θ) ^ 2 * (1 - α) ^ 2 * (1 + α) ^ 2 <
          (1 + α) ^ 2 * (1 - θ) * (1 + r) ^ 2 := by
        have h1 : (1 - θ) * (1 - α) ^ 2 < (1 + r) ^ 2 := by
          have : (1 - α) ^ 2 < 1 := by nlinarith
          have : (1 - θ) * (1 - α) ^ 2 < 1 := by nlinarith
          nlinarith
        have h2 : 0 < (1 + α) ^ 2 * (1 - θ) := by positivity
        have h3 := mul_lt_mul_of_pos_left h1 h2
        have e3 : (1 - θ) ^ 2 * (1 - α) ^ 2 * (1 + α) ^ 2 =
            (1 + α) ^ 2 * (1 - θ) * ((1 - θ) * (1 - α) ^ 2) := by ring
        rw [e3]; exact h3
      have hpos : 0 < (1 + r) ^ 2 := by positivity
      have h4 : (1 - r) ^ 2 * (1 + r) ^ 2 < ((1 + α) ^ 2 * (1 - θ)) * (1 + r) ^ 2 := by
        rw [← mul_pow, e2]; exact hlt
      exact lt_of_mul_lt_mul_right h4 hpos.le
    -- (1+α)(1-θ)v > r(1-r)
    have hmain : r * (1 - r) < (1 + α) * ((1 - θ) * v) := by
      have h0 : 0 ≤ (1 + α) * ((1 - θ) * v) := by positivity
      have h2 : (r * (1 - r)) ^ 2 < ((1 + α) * ((1 - θ) * v)) ^ 2 := by
        rw [mul_pow, mul_pow (1 + α), huv2]
        have : 0 < r ^ 2 := by positivity
        have h3 := mul_lt_mul_of_pos_left hk this
        linarith [h3, show (1 + α) ^ 2 * ((1 - θ) * r ^ 2) = r ^ 2 * ((1 + α) ^ 2 * (1 - θ)) by ring]
      exact lt_of_pow_lt_pow_left₀ 2 h0 h2
    have e : Ctil P - cOR P = P.a * α *
        (r ^ 2 - r + (1 + α) * ((1 - θ) * v)) / (P.b * (1 + α)) := by
      unfold cOR Ctil
      rw [← hα, ← hθ, ← hr, ← hv]
      rw [hr2]
      field_simp
      ring
    have : 0 < Ctil P - cOR P := by
      rw [e]
      apply div_pos _ (by positivity)
      apply mul_pos (mul_pos ha hα0)
      nlinarith
    linarith
