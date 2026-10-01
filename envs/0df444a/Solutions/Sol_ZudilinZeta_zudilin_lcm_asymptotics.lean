-- Prove2me | solution 1 for ZudilinZeta.zudilin_lcm_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T10:22:02.215818+00:00
-- url     : https://prove2.me/submissions/ce4eac8b-ee35-41a9-9401-5eb71eee3f8f

import Definitions.Def_ZudilinZetaArith
import Theorems.Thm_MediumPNT

open Filter Asymptotics ZudilinZeta
open scoped Topology

private lemma psi_div_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  have hlog : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp Real.tendsto_log_atTop
  have hexp : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg (neg_lt_zero.mpr hc))
  have hsmall : (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      =o[atTop] (fun x : ℝ => x) := by
    apply (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr
    apply hexp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [hx.ne']
  have hzero : Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / x) atTop (𝓝 0) :=
    (hO.trans_isLittleO hsmall).tendsto_div_nhds_zero
  have hlim : Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / x + 1) atTop (𝓝 1) := by
    simpa only [zero_add] using hzero.add_const 1
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp
  ring

private lemma log_lcm_mul_tendsto (m : ℕ) :
    Tendsto (fun n : ℕ => Real.log (D (m * n) : ℝ) / (n : ℝ)) atTop (𝓝 (m : ℝ)) := by
  by_cases hm : m = 0
  · subst m
    simp [D]
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hindex : Tendsto (fun n : ℕ => (m : ℝ) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hmR
  have hlim := (psi_div_tendsto_one.comp hindex).mul_const (m : ℝ)
  simp only [one_mul] at hlim
  apply hlim.congr
  intro n
  change Chebyshev.psi ((m : ℝ) * (n : ℝ)) / ((m : ℝ) * (n : ℝ)) * (m : ℝ) =
    Real.log (Nat.lcmUpto (m * n) : ℝ) / (n : ℝ)
  rw [← Chebyshev.psi_eq_log_lcmUpto, Nat.cast_mul, div_mul_eq_mul_div,
    mul_comm (Chebyshev.psi _), mul_div_mul_left _ _ hmR.ne']

theorem solution (P : Params) (j : ℕ) (hj : 1 ≤ j) (hjq : j ≤ P.q - P.r) :
    Filter.Tendsto (fun n : ℕ => Real.log (D (m P j * n) : ℝ) / (n : ℝ)) Filter.atTop
      (nhds (m P j : ℝ)) :=
  log_lcm_mul_tendsto (m P j)
