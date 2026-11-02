-- Prove2me | solution 1 for OffGridStorage.TechChoice.eq_20_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:19:14.386256+00:00
-- url     : https://prove2.me/submissions/9056f5c5-e5c5-4bc0-a24b-649de5644e7f

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

open MeasureTheory OffGridStorage.TechChoice

theorem solution (p : Params) (hp : Standing p) (Q K : ℝ) (hK : 0 ≤ K)
    (hQK : p.DH + K / p.e ≤ Q) :
    profitF p Q K = closedFormF p Q K := by
  obtain ⟨hDH, hDL, he0, he1, hcQ, hcK, hg, hT⟩ := hp
  have hKe : 0 ≤ K / p.e := div_nonneg hK he0.le
  have hQ : 0 < Q := by linarith
  set f : ℝ → ℝ := fun s => min s p.DH + min (p.e * pos (s - p.DH)) K with hf
  have hfc : Continuous f := by
    show Continuous (fun s => min s p.DH + min (p.e * max 0 (s - p.DH)) K)
    fun_prop
  have h1 : ∫ v in Set.Icc (0:ℝ) 1, (min (Q * v) p.DH + min (p.e * pos (Q * v - p.DH)) K)
      = ∫ v in (0:ℝ)..1, f (Q * v) := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]
  have h2 : ∫ v in (0:ℝ)..1, f (Q * v) = Q⁻¹ * ∫ s in (0:ℝ)..Q, f s := by
    rw [intervalIntegral.integral_comp_mul_left f hQ.ne']
    simp
  -- split into the two pieces
  have hA : Continuous (fun s : ℝ => min s p.DH) := by fun_prop
  have hB : Continuous (fun s : ℝ => min (p.e * pos (s - p.DH)) K) := by
    show Continuous (fun s : ℝ => min (p.e * max 0 (s - p.DH)) K); fun_prop
  have h3 : ∫ s in (0:ℝ)..Q, f s = (∫ s in (0:ℝ)..Q, min s p.DH) +
      ∫ s in (0:ℝ)..Q, min (p.e * pos (s - p.DH)) K :=
    intervalIntegral.integral_add (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _)
  have hDHQ : p.DH ≤ Q := by linarith
  have hIA : ∫ s in (0:ℝ)..Q, min s p.DH = p.DH ^ 2 / 2 + p.DH * (Q - p.DH) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := p.DH)
      (hA.intervalIntegrable _ _) (hA.intervalIntegrable _ _)]
    have e1 : ∫ s in (0:ℝ)..p.DH, min s p.DH = ∫ s in (0:ℝ)..p.DH, s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hDH.le] at hs
      exact min_eq_left hs.2
    have e2 : ∫ s in p.DH..Q, min s p.DH = ∫ s in p.DH..Q, p.DH := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hDHQ] at hs
      exact min_eq_right hs.1
    rw [e1, e2, integral_id, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hIB : ∫ s in (0:ℝ)..Q, min (p.e * pos (s - p.DH)) K =
      K ^ 2 / (2 * p.e) + K * (Q - p.DH - K / p.e) := by
    have hb1 : p.DH ≤ p.DH + K / p.e := by linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := p.DH)
      (hB.intervalIntegrable _ _) (hB.intervalIntegrable _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (a := p.DH) (b := p.DH + K / p.e)
      (hB.intervalIntegrable _ _) (hB.intervalIntegrable _ _)]
    have e1 : ∫ s in (0:ℝ)..p.DH, min (p.e * pos (s - p.DH)) K = ∫ s in (0:ℝ)..p.DH, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hDH.le] at hs
      unfold pos; beta_reduce
      rw [max_eq_left (by linarith [hs.2]), mul_zero, min_eq_left hK]
    have e2 : ∫ s in p.DH..(p.DH + K / p.e), min (p.e * pos (s - p.DH)) K =
        ∫ s in p.DH..(p.DH + K / p.e), (p.e * s - p.e * p.DH) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hb1] at hs
      unfold pos; beta_reduce
      rw [max_eq_right (by linarith [hs.1])]
      have : p.e * (s - p.DH) ≤ K := by
        have := hs.2
        have h' : s - p.DH ≤ K / p.e := by linarith
        rw [le_div_iff₀ he0] at h'
        linarith
      rw [min_eq_left this]; ring
    have e3 : ∫ s in (p.DH + K / p.e)..Q, min (p.e * pos (s - p.DH)) K =
        ∫ s in (p.DH + K / p.e)..Q, K := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hQK] at hs
      unfold pos; beta_reduce
      have h' : K / p.e ≤ s - p.DH := by linarith [hs.1]
      rw [div_le_iff₀ he0] at h'
      rw [max_eq_right (by nlinarith), min_eq_right (by linarith)]
    have hi1 : IntervalIntegrable (fun s : ℝ => p.e * s) volume p.DH (p.DH + K / p.e) :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun _ : ℝ => p.e * p.DH) volume p.DH (p.DH + K / p.e) :=
      continuous_const.intervalIntegrable _ _
    rw [e1, e2, e3, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul, integral_id]
    simp only [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
      smul_eq_mul]
    simp only [smul_eq_mul, sub_zero, mul_zero, zero_add]
    field_simp
    ring
  unfold profitF closedFormF
  rw [h1, h2, h3, hIA, hIB]
  field_simp
  ring
