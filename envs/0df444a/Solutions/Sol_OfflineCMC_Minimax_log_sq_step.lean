-- Prove2me | solution 1 for OfflineCMC.Minimax.log_sq_step
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:16:55.897571+00:00
-- url     : https://prove2.me/submissions/c8c62621-9e25-4908-acbf-48b48bb14558

import Mathlib
namespace OfflineCMC.Minimax

open Filter Topology

lemma part1 : ∃ c : ℝ, ∀ x : ℝ, c ≤ x →
      (1 + Real.log 2 / Real.log x + 2 * (Real.log (Real.log x) / Real.log x)) ^ 2 < 2 := by
  have hL : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have h1 : Tendsto (fun x => Real.log 2 / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have h2 : Tendsto (fun x => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hL
  have h3 : Tendsto (fun x => (1 + Real.log 2 / Real.log x +
      2 * (Real.log (Real.log x) / Real.log x)) ^ 2) atTop (𝓝 ((1 + 0 + 2 * 0) ^ 2)) :=
    ((tendsto_const_nhds.add h1).add (h2.const_mul 2)).pow 2
  have h4 := h3.eventually (gt_mem_nhds (show ((1:ℝ) + 0 + 2 * 0) ^ 2 < 2 by norm_num))
  exact Filter.eventually_atTop.1 h4

theorem log_sq_step :
    (∃ c : ℝ, ∀ x : ℝ, c < x →
      (1 + Real.log 2 / Real.log x + 2 * (Real.log (Real.log x) / Real.log x)) ^ 2 < 2) ∧
    ∃ c : ℝ, 1 < c ∧ ∀ x : ℝ, c < x → ∀ m : ℝ, 2 * x * Real.log x ^ 2 ≤ m →
      x ≤ m / Real.log m ^ 2 := by
  obtain ⟨c1, hc1⟩ := part1
  refine ⟨⟨c1, fun x hx => hc1 x hx.le⟩, ⟨max c1 (Real.exp 2), ?_, ?_⟩⟩
  · exact lt_of_lt_of_le (by have := Real.add_one_lt_exp (show (2:ℝ) ≠ 0 by norm_num); linarith)
      (le_max_right _ _)
  intro x hx m hm
  have hxc1 : c1 ≤ x := le_trans (le_max_left _ _) hx.le
  have hxe : Real.exp 2 < x := lt_of_le_of_lt (le_max_right _ _) hx
  have hx0 : 0 < x := lt_trans (Real.exp_pos 2) hxe
  set L := Real.log x with hLdef
  have hL2 : 2 < L := by rw [hLdef, Real.lt_log_iff_exp_lt hx0]; exact hxe
  have hL0 : 0 < L := by linarith
  set M0 := 2 * x * L ^ 2 with hM0
  have hM0pos : 0 < M0 := by positivity
  set v := Real.log M0 with hv
  have hvexp : Real.log M0 = Real.log 2 + L + 2 * Real.log L := by
    rw [hM0, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hx0.ne',
      Real.log_pow]; push_cast; ring
  have hloglog : 0 < Real.log L := Real.log_pos (by linarith)
  have hv2 : 2 ≤ v := by
    rw [hv, hvexp]
    have := Real.log_pos (show (1:ℝ) < 2 by norm_num)
    linarith
  have hE := hc1 x hxc1
  rw [← hLdef] at hE
  have hvsq : v ^ 2 < 2 * L ^ 2 := by
    have e : v = L * (1 + Real.log 2 / L + 2 * (Real.log L / L)) := by
      rw [hv, hvexp]; field_simp; ring
    rw [e, mul_pow]
    nlinarith [sq_nonneg L, mul_pos hL0 hL0]
  have hxv : x * v ^ 2 ≤ M0 := by
    have : x * v ^ 2 ≤ x * (2 * L ^ 2) := mul_le_mul_of_nonneg_left hvsq.le hx0.le
    rw [hM0]; linarith
  have hmpos : 0 < m := lt_of_lt_of_le hM0pos hm
  set u := Real.log m with hu
  have hvu : v ≤ u := Real.log_le_log hM0pos hm
  set d := u - v with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  have hu0 : 0 < u := by linarith
  have hu_le : u ≤ v * (1 + d / 2) := by
    have : d ≤ v * (d / 2) := by nlinarith
    rw [hd] at this ⊢; nlinarith
  have hu2 : u ^ 2 ≤ v ^ 2 * (1 + d / 2) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hu0.le hu_le 2
  have hexpd : (1 + d / 2) ^ 2 ≤ Real.exp d := by
    have := Real.quadratic_le_exp_of_nonneg hd0
    nlinarith [sq_nonneg d]
  have hM0exp : M0 = Real.exp v := by rw [hv, Real.exp_log hM0pos]
  have hmexp : m = Real.exp v * Real.exp d := by
    rw [← Real.exp_add, hd, add_sub_cancel, hu, Real.exp_log hmpos]
  have key : x * u ^ 2 ≤ m := by
    calc x * u ^ 2 ≤ x * (v ^ 2 * (1 + d / 2) ^ 2) := mul_le_mul_of_nonneg_left hu2 hx0.le
      _ = (x * v ^ 2) * (1 + d / 2) ^ 2 := by ring
      _ ≤ M0 * Real.exp d := mul_le_mul hxv hexpd (by positivity) hM0pos.le
      _ = m := by rw [hmexp, hM0exp]
  rw [le_div_iff₀ (by positivity)]
  exact key

end OfflineCMC.Minimax

theorem solution :
    (∃ c : ℝ, ∀ x : ℝ, c < x →
      (1 + Real.log 2 / Real.log x + 2 * (Real.log (Real.log x) / Real.log x)) ^ 2 < 2) ∧
    ∃ c : ℝ, 1 < c ∧ ∀ x : ℝ, c < x → ∀ m : ℝ, 2 * x * Real.log x ^ 2 ≤ m →
      x ≤ m / Real.log m ^ 2 :=
  OfflineCMC.Minimax.log_sq_step
