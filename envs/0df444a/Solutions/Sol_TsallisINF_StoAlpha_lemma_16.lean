-- Prove2me | solution 1 for TsallisINF.StoAlpha.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:39:07.874047+00:00
-- url     : https://prove2.me/submissions/f9dc1318-b3c5-4b29-aeb0-0db5dbc652e1

import Mathlib
set_option autoImplicit false

namespace TsallisINF.StoAlpha

lemma key (L β : ℝ) (hL : 0 < L) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (1 - Real.exp (-β * L)) / β ≤ L ^ (1 - β) := by
  set c : ℝ := (1 - Real.exp (-L)) / L with hcdef
  have hE : 0 < 1 - Real.exp (-L) := by
    have : Real.exp (-L) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hc : 0 < c := div_pos hE hL
  have hpt : ∀ s : ℝ, Real.exp (-β * s) ≤ c ^ β * (β * Real.exp (-s) / c + (1 - β)) := by
    intro s
    have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := β) (w₂ := 1 - β)
      (p₁ := Real.exp (-s) / c) (p₂ := 1) hβ0.le (by linarith) (by positivity) (by norm_num) (by ring)
    rw [Real.div_rpow (Real.exp_pos _).le hc.le, ← Real.exp_mul, Real.one_rpow, mul_one] at h
    have hcb : 0 < c ^ β := Real.rpow_pos_of_pos hc β
    have h2 : Real.exp (-s * β) / c ^ β * c ^ β = Real.exp (-s * β) := div_mul_cancel₀ _ hcb.ne'
    calc Real.exp (-β * s) = Real.exp (-s * β) := by ring_nf
      _ = Real.exp (-s * β) / c ^ β * c ^ β := h2.symm
      _ ≤ (β * (Real.exp (-s) / c) + (1 - β) * 1) * c ^ β := by gcongr
      _ = c ^ β * (β * Real.exp (-s) / c + (1 - β)) := by ring
  have hI1 : ∫ s in (0:ℝ)..L, Real.exp (-β * s) = (1 - Real.exp (-β * L)) / β := by
    have : ∀ x ∈ Set.uIcc (0:ℝ) L, HasDerivAt (fun s : ℝ => -Real.exp (-β * s) / β) (Real.exp (-β * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun s : ℝ => -β * s) (-β) x := by
        simpa using (hasDerivAt_id x).const_mul (-β)
      have h2 := (h1.exp).neg.div_const β
      refine h2.congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this (by apply Continuous.intervalIntegrable; fun_prop)]
    simp only [mul_zero, Real.exp_zero]
    field_simp
    ring
  have hI2 : ∫ s in (0:ℝ)..L, c ^ β * (β * Real.exp (-s) / c + (1 - β)) = c ^ β * L := by
    have : ∀ x ∈ Set.uIcc (0:ℝ) L, HasDerivAt (fun s : ℝ => c ^ β * (-β * Real.exp (-s) / c + (1 - β) * s))
        (c ^ β * (β * Real.exp (-x) / c + (1 - β))) x := by
      intro x _
      have h1 : HasDerivAt (fun s : ℝ => -s) (-1) x := by
        exact hasDerivAt_neg x
      have h2 := ((h1.exp).const_mul (-β)).div_const c
      have h3 := (h2.add ((hasDerivAt_id x).const_mul (1 - β))).const_mul (c ^ β)
      refine h3.congr_deriv ?_
      simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this (by apply Continuous.intervalIntegrable; fun_prop)]
    simp only [mul_zero, neg_zero, Real.exp_zero]
    have hcL : c * L = 1 - Real.exp (-L) := by rw [hcdef]; field_simp
    have h : (-β * Real.exp (-L) / c + (1 - β) * L) - (-β * 1 / c + 0) = L := by
      field_simp
      linear_combination (-β) * hcL
    rw [← mul_sub, h]
  have hmono : ∫ s in (0:ℝ)..L, Real.exp (-β * s) ≤ ∫ s in (0:ℝ)..L, c ^ β * (β * Real.exp (-s) / c + (1 - β)) := by
    apply intervalIntegral.integral_mono_on hL.le
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
    · intro s _; exact hpt s
  rw [hI1, hI2] at hmono
  have hc1 : c ≤ 1 / L := by
    rw [hcdef]; gcongr; have := Real.exp_pos (-L); linarith
  have hcL : c ^ β * L ≤ L ^ (1 - β) := by
    have h1 : c ^ β ≤ (1 / L) ^ β := Real.rpow_le_rpow hc.le hc1 hβ0.le
    rw [Real.div_rpow zero_le_one hL.le, Real.one_rpow] at h1
    have h3 : L ^ (1 - β) = L / L ^ β := by
      rw [Real.rpow_sub hL, Real.rpow_one]
    rw [h3]
    have hLb : 0 < L ^ β := Real.rpow_pos_of_pos hL β
    rw [le_div_iff₀ hLb]
    calc c ^ β * L * L ^ β ≤ 1 / L ^ β * L * L ^ β := by gcongr
      _ = L := by field_simp
  exact hmono.trans hcL

end TsallisINF.StoAlpha

theorem solution (α : ℝ) (hα : α ∈ Set.Ico (0 : ℝ) 1) (z : ℝ) (hz : 1 ≤ z) :
    (1 - z ^ (-1 + α)) / (1 - α) ≤ Real.log z ^ α := by
  obtain ⟨h0, h1⟩ := hα
  have hz0 : 0 < z := by linarith
  have hL : 0 ≤ Real.log z := Real.log_nonneg hz
  rcases hL.eq_or_lt with hL0 | hLpos
  · have : Real.log z = 0 := hL0.symm
    have hz1 : z = 1 := by
      rcases Real.log_eq_zero.mp this with h | h | h <;> [linarith; exact h; linarith]
    subst hz1
    simp only [Real.rpow_def_of_pos zero_lt_one, Real.log_one]
    simp
    exact Real.rpow_nonneg le_rfl _ |>.trans' le_rfl
  · have := TsallisINF.StoAlpha.key (Real.log z) (1 - α) hLpos (by linarith) (by linarith)
    have e : z ^ (-1 + α) = Real.exp (-(1 - α) * Real.log z) := by
      rw [Real.rpow_def_of_pos hz0]; ring_nf
    rw [e]
    have e2 : (1 - (1 - α)) = α := by ring
    rw [e2] at this
    exact this
