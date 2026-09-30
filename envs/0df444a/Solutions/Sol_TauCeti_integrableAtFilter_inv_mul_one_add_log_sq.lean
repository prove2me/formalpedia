-- Prove2me | solution 1 for TauCeti.integrableAtFilter_inv_mul_one_add_log_sq
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:14.378992+00:00
-- url     : https://prove2.me/submissions/602c7e0f-0a4a-4477-9596-96627219ff70

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Improper-integral asymptotics and logarithmic decay

This file extends Mathlib's improper-integral estimates with an asymptotic estimate for weighted
integrals and integrability at infinity of `(t (1 + log t) ^ 2)⁻¹`.

## Main declarations

* `TauCeti.integrableAtFilter_inv_mul_one_add_log_sq`: the function
  `t ↦ (t (1 + log t) ^ 2)⁻¹` is integrable at infinity.
* `TauCeti.isLittleO_integral_rpow_sub_one_mul`: a remainder `E t = o(t)` has
  `∫ t in 1..x, t ^ (τ - 1) * E t = o(x ^ (τ + 1))`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Asymptotics Filter MeasureTheory Set



/-- The function `(t (1 + log t) ^ 2)⁻¹` is integrable at infinity. On `Ioi 1` it is dominated
by Mathlib's log-Cauchy density `(t (1 + (log t) ^ 2))⁻¹`. -/
theorem solution :
    _root_.MeasureTheory.IntegrableAtFilter (fun u : ℝ ↦ (u * (1 + _root_.Real.log u) ^ 2)⁻¹) _root_.Filter.atTop := by
  refine ⟨_root_.Set.Ioi 2, _root_.Filter.Ioi_mem_atTop 2, ?_⟩
  have hmaj : _root_.MeasureTheory.IntegrableOn (fun u : ℝ ↦ (u * _root_.Real.log u ^ 2)⁻¹) (_root_.Set.Ioi (2 : ℝ)) :=
    (_root_.integrableOn_inv_div_log_sq_Ioi (by norm_num : (1 : ℝ) < 2)).congr_fun
      (fun u _ ↦ by simp [_root_.div_eq_mul_inv, _root_.mul_comm]) _root_.measurableSet_Ioi
  refine _root_.MeasureTheory.Integrable.mono hmaj (by fun_prop) ?_
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem _root_.measurableSet_Ioi] with u hu
  have hu1 : (1 : ℝ) < u := _root_.lt_trans (by norm_num) hu
  have hu0 : (0 : ℝ) < u := _root_.lt_trans _root_.one_pos hu1
  have hL : (0 : ℝ) ≤ _root_.Real.log u := _root_.Real.log_nonneg hu1.le
  have hLpos : (0 : ℝ) < _root_.Real.log u := _root_.Real.log_pos hu1
  rw [_root_.Real.norm_of_nonneg (by positivity), _root_.Real.norm_of_nonneg (by positivity)]
  gcongr
  nlinarith

end TauCeti

end
end
