-- Prove2me | solution 1 for Zeta23.Tail.grid_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:06:05.934283+00:00
-- url     : https://prove2.me/submissions/2337ff19-b0fd-45f0-be55-aad34bfb03a3

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_Zeta23_Tail_Basic
import Theorems.Thm_Zeta23_Tail_grid_const_bound
import Theorems.Thm_Zeta23_Tail_sum_inv_pow_four_le_telescope

-- from Zeta23.Tail.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Basic.lean — shared elementary definitions for prop:tail (the paper §4.2).
-/

noncomputable section

namespace Zeta23
namespace Tail



lemma distI_of_le {T γ : ℝ} (hT : 0 ≤ T) (h : γ ≤ T) : distI T γ = T - γ := by
  unfold distI
  have h1 : max (T - γ) (γ - 2 * T) = T - γ := max_eq_left (by linarith)
  rw [h1, max_eq_right (by linarith)]

lemma distI_of_ge {T γ : ℝ} (hT : 0 ≤ T) (h : 2 * T ≤ γ) : distI T γ = γ - 2 * T := by
  unfold distI
  have h1 : max (T - γ) (γ - 2 * T) = γ - 2 * T := max_eq_right (by linarith)
  rw [h1, max_eq_right (by linarith)]








end Tail
end Zeta23
end
end

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



/-- ∑_{k<d} (D + k h)⁻⁴ ≤ D⁻⁴ + D⁻³/(3h) for D, h > 0 (any d). -/
lemma sum_inv_pow_four_le {D h : ℝ} (hD : 0 < D) (hh : 0 < h) (d : ℕ) :
    ∑ k ∈ range d, ((D + k * h) ^ 4)⁻¹ ≤ (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h) := by
  cases d with
  | zero => simp only [range_zero, sum_empty]; positivity
  | succ d =>
    refine (sum_inv_pow_four_le_telescope hD hh d).trans ?_
    have : 0 ≤ ((D + d * h) ^ 3)⁻¹ / (3 * h) := by positivity
    calc (D ^ 4)⁻¹ + ((D ^ 3)⁻¹ - ((D + d * h) ^ 3)⁻¹) / (3 * h)
        = (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h) - ((D + d * h) ^ 3)⁻¹ / (3 * h) := by ring
      _ ≤ _ := by linarith



end Tail
end Zeta23
end
open Finset Real
open Zeta23
open Tail

theorem solution {T L γ : ℝ} {d : ℕ} (hL : 2 ≤ L) (hT : 0 < T)
    (hd : (d : ℝ) * (2 * π / L) ≤ T) (hD : 1 ≤ distI T γ) :
    ∑ k ∈ range d, (|γ - (T + k * (2 * π / L))| ^ 4)⁻¹ ≤ L * ((distI T γ) ^ 3)⁻¹ := by
  set h := 2 * π / L with hh_def
  have hLpos : 0 < L := by linarith
  have hh : 0 < h := by positivity
  -- γ is at distance ≥ 1 from I, so it lies on one side of it.
  have hside : 1 ≤ T - γ ∨ 1 ≤ γ - 2 * T := by
    unfold distI at hD
    rcases le_max_iff.mp hD with h0 | h1
    · exact absurd h0 (by norm_num)
    · exact le_max_iff.mp h1
  rcases hside with hlt | hgt
  · -- γ below I: |γ − τ_k| = D + k h with D = T − γ.
    have hDeq : distI T γ = T - γ := distI_of_le hT.le (by linarith)
    rw [hDeq] at hD ⊢
    have hterm : ∀ k ∈ range d,
        (|γ - (T + k * h)| ^ 4)⁻¹ = ((T - γ + k * h) ^ 4)⁻¹ := by
      intro k _
      have hk : 0 ≤ (k : ℝ) * h := by positivity
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [sum_congr rfl hterm]
    exact (sum_inv_pow_four_le (by linarith) hh d).trans (grid_const_bound hD hL)
  · -- γ above I: reflect k ↦ d−1−k; |γ − τ_{d−1−k}| ≥ D + k h with D = γ − 2T.
    have hDeq : distI T γ = γ - 2 * T := distI_of_ge hT.le (by linarith)
    rw [hDeq] at hD ⊢
    have hD0 : 0 < γ - 2 * T := by linarith
    rw [← sum_range_reflect]
    have hterm : ∀ k ∈ range d,
        (|γ - (T + ((d - 1 - k : ℕ) : ℝ) * h)| ^ 4)⁻¹ ≤ ((γ - 2 * T + k * h) ^ 4)⁻¹ := by
      intro k hk
      have hkd : k < d := mem_range.mp hk
      have hcast : ((d - 1 - k : ℕ) : ℝ) = d - 1 - k := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
      rw [hcast]
      have hk0 : 0 ≤ (k : ℝ) * h := by positivity
      -- τ_{d-1-k} = T + (d-1-k)h ≤ T + d h − h − k h ≤ 2T − h − k h
      have hle : T + ((d : ℝ) - 1 - k) * h ≤ 2 * T - h - k * h := by nlinarith
      have hpos : γ - 2 * T + k * h ≤ γ - (T + ((d : ℝ) - 1 - k) * h) := by linarith
      have hpos' : 0 < γ - 2 * T + k * h := by linarith
      rw [abs_of_pos (by linarith)]
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ hpos'.le hpos 4
    exact (sum_le_sum hterm).trans
      ((sum_inv_pow_four_le hD0 hh d).trans (grid_const_bound hD hL))
