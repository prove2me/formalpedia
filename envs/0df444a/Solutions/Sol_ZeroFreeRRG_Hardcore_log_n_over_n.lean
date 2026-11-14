-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.log_n_over_n
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:14.454633+00:00
-- url     : https://prove2.me/submissions/c4417754-b520-4453-8b8c-f60084f600cb

import Mathlib
set_option autoImplicit false
open Filter Topology

theorem solution (C : ℝ) : Tendsto (fun n : ℕ => -C * Real.log ((n:ℝ)+1) / n) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 (by norm_num)).comp hn
  have hh' : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+1) / n) atTop (𝓝 0) := by
    convert hh using 1 <;> funext n <;> simp
  have hh'' := hh'.const_mul (-C)
  simpa only [mul_zero,mul_div_assoc] using hh''
