-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P44.large_repeaters
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:10:24.622944+00:00
-- url     : https://prove2.me/submissions/0cacc228-0fc9-406f-9ba0-f16ee5559c47

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P44
open QAlgorithms.Papers.Independent.Advance50.P44
open Filter Topology

theorem solution (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) :
    Tendsto (fun N : ℕ => equalSpacingLossExpression eta N -
      (Real.logb 2 (N : ℝ) - Real.logb 2 (Real.log (1 / eta))))
      atTop (nhds 0) := by
  set L : ℝ := Real.log (1 / eta) with hL
  have hLpos : 0 < L := Real.log_pos (by rw [one_div]; exact one_lt_inv₀ heta0 |>.mpr heta1)
  -- g(t) = (1 - exp(-t))/t → 1 as t → 0+
  have hd : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) 1 0 := by
    have h1 : HasDerivAt (fun t : ℝ => -t) (-1) 0 := hasDerivAt_neg 0
    have h2 := (Real.hasDerivAt_exp (-(0:ℝ))).comp 0 h1
    have h3 := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub h2
    have h3' : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (0 - Real.exp (-(0:ℝ)) * -1) 0 := h3
    exact h3'.congr_deriv (by simp)
  have hs : Tendsto (slope (fun t : ℝ => 1 - Real.exp (-t)) 0) (𝓝[≠] 0) (𝓝 1) :=
    hasDerivAt_iff_tendsto_slope.mp hd
  have hs' : Tendsto (slope (fun t : ℝ => 1 - Real.exp (-t)) 0) (𝓝[>] 0) (𝓝 1) :=
    hs.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  have hTpos : ∀ N : ℕ, 0 < L / ((N : ℝ) + 1) := fun N => div_pos hLpos (by positivity)
  have ht : Tendsto (fun N : ℕ => L / ((N : ℝ) + 1)) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall hTpos⟩
    have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact h1.const_div_atTop L
  have hg := hs'.comp ht
  have hg1 : Tendsto (fun N : ℕ => Real.log ((slope (fun t : ℝ => 1 - Real.exp (-t)) 0) (L / ((N : ℝ) + 1)))) atTop (𝓝 0) := by
    have := (Real.continuousAt_log (show (1:ℝ) ≠ 0 by norm_num)).tendsto.comp hg
    rw [Real.log_one] at this
    exact this
  have hg2 : Tendsto (fun N : ℕ => Real.log (1 + 1 / (N : ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    have := (Real.continuousAt_log (show (1 + 0 : ℝ) ≠ 0 by norm_num)).tendsto.comp h
    rw [add_zero, Real.log_one] at this
    exact this
  have hall : Tendsto (fun N : ℕ => (Real.log (1 + 1 / (N : ℝ)) -
      Real.log ((slope (fun t : ℝ => 1 - Real.exp (-t)) 0) (L / ((N : ℝ) + 1)))) / Real.log 2)
      atTop (𝓝 0) := by
    have := (hg2.sub hg1).div_const (Real.log 2)
    simpa using this
  refine hall.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hT := hTpos N
  have hexp : eta ^ (1 / ((N : ℝ) + 1)) = Real.exp (-(L / ((N : ℝ) + 1))) := by
    rw [Real.rpow_def_of_pos heta0]
    congr 1
    have h0 : Real.log (1 / eta) = - Real.log eta := by rw [one_div, Real.log_inv]
    rw [hL, h0]
    ring
  have hlt : Real.exp (-(L / ((N : ℝ) + 1))) < 1 := by
    have := Real.exp_lt_exp.mpr (show -(L / ((N : ℝ) + 1)) < 0 by linarith)
    simpa using this
  have hslope : (slope (fun t : ℝ => 1 - Real.exp (-t)) 0) (L / ((N : ℝ) + 1)) =
      (1 - Real.exp (-(L / ((N : ℝ) + 1)))) / (L / ((N : ℝ) + 1)) := by
    rw [slope_def_field]; simp
  have hgpos : 0 < (1 - Real.exp (-(L / ((N : ℝ) + 1)))) := by linarith
  simp only [equalSpacingLossExpression, Real.logb]
  rw [hexp, hslope, Real.log_div hgpos.ne' hT.ne', Real.log_div hLpos.ne' (by positivity)]
  have h1 : Real.log (1 + 1 / (N : ℝ)) = Real.log ((N:ℝ) + 1) - Real.log N := by
    rw [show (1 + 1 / (N : ℝ)) = ((N:ℝ) + 1) / N by field_simp, Real.log_div (by positivity) hNpos.ne']
  rw [h1]
  field_simp
  ring
