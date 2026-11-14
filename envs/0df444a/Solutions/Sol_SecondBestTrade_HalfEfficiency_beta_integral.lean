-- Prove2me | solution 1 for SecondBestTrade.HalfEfficiency.beta_integral
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-13T15:25:58.987613+00:00
-- url     : https://prove2.me/submissions/4f0eb1fb-f03f-4e35-b815-54b0dfc6eda7

import Definitions.Def_SecondBestTrade_HalfEfficiency_Clocks

open MeasureTheory Set SecondBestTrade.HalfEfficiency

noncomputable section

theorem solution (tau : ℝ) (htau : 0 ≤ tau) :
    IntegrableOn (betaIntegrand tau) (Ioo (0 : ℝ) 1) ∧
    betaValue tau < 2 * (1 + tau) := by
  let r := -kappa tau
  let f := fun x : ℝ => x ^ r
  let g := fun x : ℝ => (1 - x) ^ r
  have hd : 0 < 1 + tau := by linarith
  have hr : -1 < r := by
    dsimp [r, kappa]
    have := (div_lt_one hd).2 (show tau < 1 + tau by linarith)
    linarith
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hf : IntervalIntegrable f volume 0 1 := intervalIntegral.intervalIntegrable_rpow' hr
  have hg : IntervalIntegrable g volume 0 1 := by
    simpa [g, f] using (hf.comp_sub_left 1).symm
  have hfi := (intervalIntegrable_iff_integrableOn_Ioo_of_le h01).mp hf
  have hgi := (intervalIntegrable_iff_integrableOn_Ioo_of_le h01).mp hg
  have hsum := hfi.add hgi
  have hlt (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      betaIntegrand tau x < f x + g x := by
    obtain ⟨hxl, hxu⟩ := hx
    have hyl : 0 < 1 - x := by linarith
    have hyu : 1 - x < 1 := by linarith
    have hxpow := Real.rpow_lt_one hxl.le hxu (show 0 < r + 1 by linarith)
    have hypow := Real.rpow_lt_one hyl.le hyu (show 0 < r + 1 by linarith)
    rw [Real.rpow_add_one hxl.ne'] at hxpow
    rw [Real.rpow_add_one hyl.ne'] at hypow
    have h₁ := mul_lt_mul_of_pos_right hxpow (Real.rpow_pos_of_pos hyl r)
    have h₂ := mul_lt_mul_of_pos_left hypow (Real.rpow_pos_of_pos hxl r)
    change x ^ r * (1 - x) ^ r < x ^ r + (1 - x) ^ r
    linarith only [show x ^ r * (1 - x) ^ r = x ^ r * x * (1 - x) ^ r +
        x ^ r * ((1 - x) ^ r * (1 - x)) by ring, h₁, h₂]
  have hle : betaIntegrand tau ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f + g :=
    (ae_restrict_mem measurableSet_Ioo).mono (fun x hx => (hlt x hx).le)
  have hi : IntegrableOn (betaIntegrand tau) (Ioo (0 : ℝ) 1) := by
    apply hsum.mono'
    · unfold betaIntegrand
      fun_prop
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact (hlt x hx).le
      · exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _)
  have hstrict : betaValue tau < ∫ x in Ioo (0 : ℝ) 1, (f + g) x := by
    refine lt_of_le_of_ne (integral_mono_ae hi hsum hle) ?_
    intro he
    have hae := (integral_eq_iff_of_ae_le hi hsum hle).mp he
    obtain ⟨x, hx, heq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (show volume (Ioo (0 : ℝ) 1) ≠ 0 by simp) hae
    exact (hlt x hx).ne heq
  have val : (∫ x in (0 : ℝ)..1, f x) = 1 + tau := by
    dsimp [f]
    rw [integral_rpow (Or.inl hr), Real.one_rpow, Real.zero_rpow (by linarith : r + 1 ≠ 0)]
    dsimp [r, kappa]
    field_simp
    <;> ring
  have val' : (∫ x in (0 : ℝ)..1, g x) = 1 + tau := by
    change (∫ x in (0 : ℝ)..1, f (1 - x)) = _
    simpa using (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) f 1).trans
      (by simpa using val)
  rw [intervalIntegral.integral_of_le h01, integral_Ioc_eq_integral_Ioo] at val val'
  refine ⟨hi, hstrict.trans_eq ?_⟩
  change (∫ x in Ioo (0 : ℝ) 1, f x + g x) = _
  rw [integral_add hfi hgi, val, val']
  ring
