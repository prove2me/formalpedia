-- Prove2me | solution 1 for Transcendence.siegel_small_values
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:35:05.493311+00:00
-- url     : https://prove2.me/submissions/e5cf1b39-9849-4452-8a4d-588716f4c82b

import Mathlib
import Theorems.Thm_Transcendence_siegel_small_values_of_count
import Theorems.Thm_Transcendence_siegel_small_values_parameters

/-!
# An auxiliary function with small values (Waldschmidt, DALAG Prop. 4.10)

The proof follows the book (§4.5, Lemmas 4.11–4.13) with three changes, each of which only
improves constants: Dirichlet's box principle with `ℓ` cells per form, and `|z| ≤ |Re z| + |Im z|`
(a factor `2` instead of `√2`); Cauchy's inequalities on the polydisc for the Taylor coefficients;
and, in place of Schwarz and Parseval, Cauchy on the lines through the origin for the tail.

1. `Transcendence.siegel_small_values_parameters` takes `T = ⌈(4/3) W / log(R/r)⌉`, `X = ⌊e^N⌋`
   and `ℓ = ⌈(8/3) Tⁿ e^W⌉`, so that `ℓ^{2Tⁿ} < (X + 1)^L`.
2. `r < R`, as `R ≥ e r`.
3. `Transcendence.siegel_small_values_of_count` with `C = e^U` gives `p ≠ 0` with
   `|p_λ| ≤ X ≤ e^N`, and the value bound `(3/4) e^{-V} + (1/4) e^{-V}` on the polydisc of
   radius `r`.
-/

-- The statement's `hN`, `hU` and `hV` are not needed: `W ≥ 12n²` suffices.
set_option linter.unusedVariables false in
theorem solution {ι Λ : Type*} [Fintype ι] [Fintype Λ] (hι : 0 < Fintype.card ι)
    (φ : Λ → (ι → ℂ) → ℂ) (hφ : ∀ l, AnalyticOnNhd ℂ (φ l) Set.univ)
    {N U V r R : ℝ} (hN : 0 < N) (hU : 0 < U) (hV : 0 < V) (hr : 0 < r)
    (hW : 12 * (Fintype.card ι : ℝ) ^ 2 ≤ N + U + V)
    (hRe : Real.exp 1 * r ≤ R) (hRW : R ≤ r * Real.exp ((N + U + V) / 6))
    (B : Λ → ℝ) (hB : ∀ l, ∀ z ∈ Metric.closedBall (0 : ι → ℂ) R, ‖φ l z‖ ≤ B l)
    (hBU : ∑ l, B l ≤ Real.exp U)
    (hmain : (2 * (N + U + V)) ^ (Fintype.card ι + 1) ≤
      Fintype.card Λ * N * Real.log (R / r) ^ Fintype.card ι) :
    ∃ p : Λ → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp N) ∧
      ∀ z ∈ Metric.closedBall (0 : ι → ℂ) r, ‖∑ l, (p l : ℂ) * φ l z‖ ≤ Real.exp (-V) := by
  obtain ⟨T, X, ℓ, hℓ, hX, hcount, hhead, htail⟩ :=
    Transcendence.siegel_small_values_parameters hι hr hW hRe hRW hmain
  have hrR : r < R := by
    have he : 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith
  obtain ⟨p, hp0, hpX, hp⟩ := Transcendence.siegel_small_values_of_count φ hφ hr hrR B hB
    (Real.exp_pos U) hBU hℓ hcount
  refine ⟨p, hp0, fun l => ?_, fun z hz => (hp z hz).trans (by linarith)⟩
  rw [← Int.cast_abs]
  exact le_trans (by exact_mod_cast hpX l) hX
