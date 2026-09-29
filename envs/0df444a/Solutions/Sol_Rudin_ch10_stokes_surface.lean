-- Prove2me | solution 1 for Rudin.ch10_stokes_surface
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T21:41:20.55137+00:00
-- url     : https://prove2.me/submissions/5114c454-f931-4b01-996f-8bc4f8a0c6ab

import Mathlib
import Definitions.Def_Rudin_ch10_forms
import Theorems.Thm_Rudin_ch10_stokes

open Filter Topology MeasureTheory
open Rudin

/-!
# Stokes' theorem for a single `(m+1)`-surface

Rudin's Theorem 10.33 for chains (`Rudin.ch10_stokes`) is already proved on the platform.  A single
surface `Φ` is the chain `Ψ = ⟨[(1, Φ)]⟩` with one term of multiplicity `1`, and for such a chain
both sides of the chain statement collapse to the single-surface expressions:

* `Chain.integral η ⟨[(1, Φ)]⟩ = (1 : ℝ) * integralOverSimplex η Φ = integralOverSimplex η Φ`;
* `Chain.boundary ⟨[(1, Φ)]⟩` has terms `(surfaceBoundary Φ).terms.map (fun s => (1 * s.1, s.2))`,
  which is literally `(surfaceBoundary Φ).terms`, so
  `Chain.integral ω (Chain.boundary ⟨[(1, Φ)]⟩) = Chain.integral ω (surfaceBoundary Φ)`.

So the theorem is the specialisation of the chain version to a one-term chain.
-/

/-- The one-term chain of multiplicity `1` carried by a surface `Φ`. -/
private def oneChain {k n : ℕ} (Φ : SimplexSurface k n) : Chain k n := ⟨[((1 : ℤ), Φ)]⟩

/-- The integral of a form over the one-term chain of `Φ` is its integral over `Φ`. -/
private lemma integral_oneChain {k n : ℕ} (η : KForm k n) (Φ : SimplexSurface k n) :
    Chain.integral η (oneChain Φ) = integralOverSimplex η Φ := by
  simp [oneChain, Chain.integral]

/-- The boundary of the one-term chain of `Φ` has the same terms as the boundary chain of `Φ`. -/
private lemma boundary_oneChain_terms {m n : ℕ} (Φ : SimplexSurface (m + 1) n) :
    (Chain.boundary (oneChain Φ)).terms = (surfaceBoundary Φ).terms := by
  simp [oneChain, Chain.boundary]

/-- Hence the integral over the boundary of the one-term chain is the integral over the boundary
chain of the surface. -/
private lemma integral_boundary_oneChain {m n : ℕ} (ω : KForm m n)
    (Φ : SimplexSurface (m + 1) n) :
    Chain.integral ω (Chain.boundary (oneChain Φ)) = Chain.integral ω (surfaceBoundary Φ) := by
  simp only [Chain.integral, boundary_oneChain_terms]

/-- Rudin, Theorem 10.33 (Stokes' theorem) for a single `(m+1)`-surface. -/
theorem solution (m n : ℕ) (V : Set (Fin n → ℝ)) (hV : IsOpen V)
    (Φ : Rudin.SimplexSurface (m + 1) n) (hΦ : ContDiff ℝ 2 Φ.map)
    (hΦV : ∀ u ∈ Rudin.stdSimplex (m + 1), Φ.map u ∈ V)
    (ω : Rudin.KForm m n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) V) :
    Rudin.integralOverSimplex (Rudin.extDeriv ω) Φ
      = Rudin.Chain.integral ω (Rudin.surfaceBoundary Φ) := by
  have hΨ : ∀ t ∈ (oneChain Φ).terms, ContDiff ℝ 2 t.2.map ∧
      ∀ u ∈ Rudin.stdSimplex (m + 1), t.2.map u ∈ V := by
    intro t ht
    have ht' : t ∈ [((1 : ℤ), Φ)] := ht
    have ht'' : t = ((1 : ℤ), Φ) := List.mem_singleton.mp ht'
    subst ht''
    exact ⟨hΦ, hΦV⟩
  have key : Rudin.Chain.integral (Rudin.extDeriv ω) (oneChain Φ)
      = Rudin.Chain.integral ω (oneChain Φ).boundary :=
    Rudin.ch10_stokes m n V hV (oneChain Φ) hΨ ω hω
  rw [integral_oneChain, integral_boundary_oneChain] at key
  exact key
