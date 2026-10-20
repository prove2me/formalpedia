-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P02.broadcast_largeGainLimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:13:11.458947+00:00
-- url     : https://prove2.me/submissions/f47aea53-83b5-434e-ba05-e5fc553691bf

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P02

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Frontier18 QAlgorithms.Papers.Independent.Frontier18.P02

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

theorem g52d_te {x : ℝ} (hx : 0 < x) :
    thermalEntropy x = (Real.log (x + 1) + x * Real.log (1 + 1 / x)) / Real.log 2 := by
  unfold thermalEntropy
  have h : Real.log (1 + 1 / x) = Real.log (x + 1) - Real.log x := by
    rw [show (1:ℝ) + 1 / x = (x + 1) / x by field_simp,
      Real.log_div (by positivity) hx.ne']
  rw [h]; ring

theorem g52d_A : Tendsto (fun x : ℝ => x * Real.log (1 + 1 / x)) atTop (nhds 1) :=
  Real.tendsto_mul_log_one_add_div_atTop 1

theorem g52d_lim (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun G : ℝ => thermalEntropy (a * G + c) - thermalEntropy (b * G + d)) atTop
      (nhds (Real.logb 2 (a / b))) := by
  have t1 : Tendsto (fun G : ℝ => a * G + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c (tendsto_id.const_mul_atTop ha)
  have t2 : Tendsto (fun G : ℝ => b * G + d) atTop atTop :=
    tendsto_atTop_add_const_right _ d (tendsto_id.const_mul_atTop hb)
  have hA1 := g52d_A.comp t1
  have hA2 := g52d_A.comp t2
  have hinv := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have hq : Tendsto (fun G : ℝ => (a + (c + 1) * G⁻¹) / (b + (d + 1) * G⁻¹)) atTop
      (nhds ((a + (c + 1) * 0) / (b + (d + 1) * 0))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).div
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)) (by simp; linarith)
  have hlog := hq.log (by simp; exact ⟨ha.ne', hb.ne'⟩)
  have hF := ((hlog.add hA1).sub hA2).div_const (Real.log 2)
  have hlim : (Real.log ((a + (c + 1) * 0) / (b + (d + 1) * 0)) + 1 - 1) / Real.log 2 =
      Real.logb 2 (a / b) := by
    simp [Real.logb]
  rw [hlim] at hF
  refine hF.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ), t1.eventually_gt_atTop 0,
    t2.eventually_gt_atTop 0] with G hG h1 h2
  simp only [Function.comp]
  rw [g52d_te h1, g52d_te h2]
  have hG' : G ≠ 0 := hG.ne'
  have e : (a + (c + 1) * G⁻¹) / (b + (d + 1) * G⁻¹) = (a * G + c + 1) / (b * G + d + 1) := by
    rw [show a + (c + 1) * G⁻¹ = (a * G + c + 1) / G by field_simp; ring,
      show b + (d + 1) * G⁻¹ = (b * G + d + 1) / G by field_simp; ring,
      div_div_div_cancel_right₀ hG']
  rw [e, Real.log_div (by linarith) (by linarith)]
  ring

/-- PDF pp.8--9, (67): pointwise large-gain limits of (40)--(41), including
lambda=0 and lambda=1, and their exact parametrization of the nonnegative
linear trade-off triangle. For noise>0 this is a limit of explicit achievable
bounds; it does not assert an unconditional operational capacity formula. -/
theorem solution (budget noise : ℝ)
    (hbudget : 0 < budget) (hnoise : 0 ≤ noise) :
    (∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
      Tendsto (fun gain : ℝ => broadcastBobBoundary gain budget noise lambda)
        atTop (nhds (Real.logb 2 (1 + lambda * budget / (noise + 1)))) ∧
      Tendsto (fun gain : ℝ => broadcastCharlieBoundary gain budget noise lambda)
        atTop (nhds (Real.logb 2 ((budget + noise + 1) /
          (lambda * budget + noise + 1))))) ∧
    {rates : ℝ × ℝ | 0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧
      ∃ lambda : ℝ, 0 ≤ lambda ∧ lambda ≤ 1 ∧
        rates.1 ≤ Real.logb 2 (1 + lambda * budget / (noise + 1)) ∧
        rates.2 ≤ Real.logb 2 ((budget + noise + 1) /
          (lambda * budget + noise + 1))} =
    {rates : ℝ × ℝ | 0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧
      rates.1 + rates.2 ≤ Real.logb 2 (1 + budget / (noise + 1))} := by
  have hn1 : 0 < noise + 1 := by linarith
  refine ⟨fun lambda hl0 hl1 => ⟨?_, ?_⟩, ?_⟩
  · have h := g52d_lim (lambda * budget + noise + 1) (noise + 1) (-(noise + 1)) (-(noise + 1))
      (by positivity) hn1
    have e : (lambda * budget + noise + 1) / (noise + 1) = 1 + lambda * budget / (noise + 1) := by
      field_simp; ring
    rw [e] at h
    refine h.congr (fun G => ?_)
    simp only [broadcastBobBoundary]
    congr 1 <;> (congr 1; ring)
  · have h := g52d_lim (budget + noise + 1) (lambda * budget + noise + 1) (-(budget + 1))
      (-(lambda * budget + 1)) (by positivity) (by positivity)
    refine h.congr (fun G => ?_)
    simp only [broadcastCharlieBoundary]
    congr 1 <;> (congr 1; ring)
  · have key : ∀ l : ℝ, 0 ≤ l → Real.logb 2 (1 + l * budget / (noise + 1)) +
        Real.logb 2 ((budget + noise + 1) / (l * budget + noise + 1)) =
        Real.logb 2 (1 + budget / (noise + 1)) := by
      intro l hl
      have h1 : 0 < 1 + l * budget / (noise + 1) := by positivity
      have h2 : 0 < (budget + noise + 1) / (l * budget + noise + 1) := by positivity
      rw [← Real.logb_mul h1.ne' h2.ne']
      congr 1
      field_simp
      ring
    ext ⟨r1, r2⟩
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, l, hl0, hl1, hr1, hr2⟩
      refine ⟨h1, h2, ?_⟩
      have := key l hl0
      linarith
    · rintro ⟨h1, h2, hs⟩
      have hcont : ContinuousOn (fun l : ℝ => Real.logb 2 (1 + l * budget / (noise + 1)))
          (Set.Icc 0 1) := by
        simp only [Real.logb]
        refine ContinuousOn.div_const (ContinuousOn.log ?_ ?_) _
        · exact (continuousOn_const.add ((continuousOn_id.mul continuousOn_const).div_const _))
        · intro l hl
          have : 0 ≤ l := hl.1
          positivity
      have hivt := intermediate_value_Icc (zero_le_one' ℝ) hcont
      have hmem : r1 ∈ Set.Icc (Real.logb 2 (1 + 0 * budget / (noise + 1)))
          (Real.logb 2 (1 + 1 * budget / (noise + 1))) := by
        simp only [zero_mul, zero_div, add_zero, Real.logb_one, one_mul]
        exact ⟨h1, by linarith⟩
      obtain ⟨l, ⟨hl0, hl1⟩, hl⟩ := hivt hmem
      refine ⟨h1, h2, l, hl0, hl1, hl.ge, ?_⟩
      have := key l hl0
      simp only at hl
      linarith


end

