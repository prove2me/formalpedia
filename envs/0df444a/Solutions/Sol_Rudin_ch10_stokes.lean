-- Prove2me | solution 1 for Rudin.ch10_stokes
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T00:28:35.507205+00:00
-- url     : https://prove2.me/submissions/4b106d6f-1ab0-4e5e-b5dd-7fade9dc1d0f

import Mathlib
import Definitions.Def_Rudin_ch10_forms
import Theorems.Thm_Rudin_ch10_stokes_surface

open Filter Topology MeasureTheory

namespace RudinAux

open Rudin

/-- A chain integral of a form over the boundary of a chain splits as the sum, over the terms of
the chain, of the boundary integrals of the individual surfaces. -/
lemma chain_integral_boundary_aux {m n : ℕ} (ω : KForm m n)
    (L : List (ℤ × SimplexSurface (m + 1) n)) :
    ((L.flatMap fun t => (surfaceBoundary t.2).terms.map fun s => (t.1 * s.1, s.2)).map
        fun t => (t.1 : ℝ) * integralOverSimplex ω t.2).sum
      = (L.map fun t => (t.1 : ℝ) * Chain.integral ω (surfaceBoundary t.2)).sum := by
  induction L with
  | nil => simp
  | cons t ts ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.map_map, ih, List.sum_cons]
      congr 1
      simp only [Chain.integral, Function.comp_def]
      rw [← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
      push_cast
      ring

end RudinAux

open Rudin in
/-- Rudin, Theorem 10.33 (Stokes' theorem): if `Ψ` is a `(m+1)`-chain of class `C''` in an open
set `V ⊆ ℝⁿ` and `ω` is an `m`-form of class `C'` in `V`, then the integral of `dω` over
`Ψ` equals the integral of `ω` over the boundary `∂Ψ`. -/
theorem solution (m n : ℕ) (V : Set (Fin n → ℝ)) (hV : IsOpen V) (Ψ : Chain (m + 1) n)
    (hΨ : ∀ t ∈ Ψ.terms, ContDiff ℝ 2 t.2.map ∧ ∀ u ∈ Rudin.stdSimplex (m + 1), t.2.map u ∈ V)
    (ω : KForm m n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) V) :
    Chain.integral (extDeriv ω) Ψ = Chain.integral ω Ψ.boundary := by
  rw [Chain.integral, Chain.integral, Chain.boundary,
    RudinAux.chain_integral_boundary_aux ω Ψ.terms]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  obtain ⟨hsmooth, hmem⟩ := hΨ t ht
  rw [ch10_stokes_surface m n V hV t.2 hsmooth hmem ω hω]
