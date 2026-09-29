-- Prove2me | solution 1 for Zeta23.Tail.sum_inv_pow_four_le_telescope
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:07:00.586034+00:00
-- url     : https://prove2.me/submissions/daf2d70f-5fdc-4aeb-9b5f-740bd73f5453

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_Zeta23_Tail_Basic

-- from Zeta23.Tail.Grid
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Grid.lean — the grid sum in the proof of [prop:tail] (the paper §4.2).


Paper, verbatim: "Let D := dist(γ, I) ≥ D₀. The points τ_k, 0 ≤ k < d, lie in I with
spacing h = 2π/L, so ‖u_ρ‖₂² ≤ C₁²X^{1/2} ∑_{0≤k<d} |γ−τ_k|⁻⁴
≤ C₁²X^{1/2}(D⁻⁴ + (L/2π)·D⁻³/3) ≤ C₁²X^{1/2} L D⁻³ (as D ≥ 1, L ≥ 2)."
Here τ_k := T + k h [eq:fk], h := 2π/L, d := ⌊T/h⌋ so that τ_0,…,τ_{d−1} ∈ [T, 2T).
We prove the pure inequality ∑_{k<d} |γ − τ_k|⁻⁴ ≤ L·D⁻³ (the constant C₁²X^{1/2} is
threaded in Zeta23/Tail.lean), replacing the integral comparison by a telescoping sum.
-/

noncomputable section

open Finset Real

namespace Zeta23
namespace Tail

/-- Telescoping replacement for ∫ x⁻⁴: for a > 0, h > 0, h·(a+h)⁻⁴ ≤ (a⁻³ − (a+h)⁻³)/3. -/
lemma inv_pow_four_step {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    h * ((a + h) ^ 4)⁻¹ ≤ ((a ^ 3)⁻¹ - ((a + h) ^ 3)⁻¹) / 3 := by
  have hah : 0 < a + h := by linarith
  rw [← sub_nonneg]
  have key : ((a ^ 3)⁻¹ - ((a + h) ^ 3)⁻¹) / 3 - h * ((a + h) ^ 4)⁻¹
      = (6 * a ^ 2 * h ^ 2 + 4 * a * h ^ 3 + h ^ 4) / (3 * a ^ 3 * (a + h) ^ 4) := by
    field_simp
    ring
  rw [key]
  positivity





end Tail
end Zeta23
end
open Finset Real
open Zeta23
open Tail

theorem solution {D h : ℝ} (hD : 0 < D) (hh : 0 < h) (d : ℕ) :
    ∑ k ∈ range (d + 1), ((D + k * h) ^ 4)⁻¹
      ≤ (D ^ 4)⁻¹ + ((D ^ 3)⁻¹ - ((D + d * h) ^ 3)⁻¹) / (3 * h) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ]
    have hstep := inv_pow_four_step (a := D + d * h) (h := h) (by positivity) hh
    have hstep' : ((D + ((d + 1 : ℕ) : ℝ) * h) ^ 4)⁻¹
        ≤ (((D + d * h) ^ 3)⁻¹ - ((D + ((d + 1 : ℕ) : ℝ) * h) ^ 3)⁻¹) / (3 * h) := by
      have e : D + ((d + 1 : ℕ) : ℝ) * h = D + d * h + h := by push_cast; ring
      rw [e, le_div_iff₀ (by positivity)]
      calc ((D + d * h + h) ^ 4)⁻¹ * (3 * h) = 3 * (h * ((D + d * h + h) ^ 4)⁻¹) := by ring
        _ ≤ 3 * ((((D + d * h) ^ 3)⁻¹ - ((D + d * h + h) ^ 3)⁻¹) / 3) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ = _ := by ring
    calc _ ≤ (D ^ 4)⁻¹ + ((D ^ 3)⁻¹ - ((D + d * h) ^ 3)⁻¹) / (3 * h)
            + (((D + d * h) ^ 3)⁻¹ - ((D + ((d + 1 : ℕ) : ℝ) * h) ^ 3)⁻¹) / (3 * h) :=
          add_le_add ih hstep'
      _ = _ := by ring
