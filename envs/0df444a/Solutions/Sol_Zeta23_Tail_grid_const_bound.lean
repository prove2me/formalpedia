-- Prove2me | solution 1 for Zeta23.Tail.grid_const_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:07:44.518755+00:00
-- url     : https://prove2.me/submissions/bfc65e85-7c05-44d7-9f2f-8cef62c7944d

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






end Tail
end Zeta23
end
open Finset Real
open Zeta23
open Tail

theorem solution {D L : ℝ} (hD : 1 ≤ D) (hL : 2 ≤ L) :
    (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * (2 * π / L)) ≤ L * (D ^ 3)⁻¹ := by
  have hD0 : 0 < D := by linarith
  have hπ : 2 ≤ π := Real.two_le_pi
  have h1 : (D ^ 4)⁻¹ ≤ (D ^ 3)⁻¹ := by
    apply inv_anti₀ (by positivity)
    calc D ^ 3 = D ^ 3 * 1 := by ring
      _ ≤ D ^ 3 * D := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = D ^ 4 := by ring
  have h2 : (D ^ 3)⁻¹ / (3 * (2 * π / L)) = (L / (6 * π)) * (D ^ 3)⁻¹ := by
    field_simp
    ring
  rw [h2]
  have h3 : L / (6 * π) ≤ L / 2 := by
    apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  have hD3 : 0 ≤ (D ^ 3)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h3 hD3]
