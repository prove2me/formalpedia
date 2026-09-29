-- Prove2me | solution 1 for Rudin.ch10_poincare_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T00:20:26.794498+00:00
-- url     : https://prove2.me/submissions/ad6af6b5-be64-426a-9b28-2454d9dbba3b

import Mathlib
import Definitions.Def_Rudin_ch10_forms
import Theorems.Thm_Rudin_ch10_integral_alternation
import Theorems.Thm_Rudin_ch10_closed_pointwise
import Theorems.Thm_Rudin_ch10_primitive_of_closed

open Filter Topology MeasureTheory

open Rudin in
/-- Rudin, Theorem 10.39 (Poincaré's lemma): on a convex open set every closed form of positive
order and class `C'` is exact.  Closedness and exactness are expressed through integrals over
surfaces lying in `E`, since a form is determined by those integrals. -/
theorem solution (m n : ℕ) (E : Set (Fin n → ℝ)) (hE : IsOpen E) (hconv : Convex ℝ E)
    (ω : KForm (m + 1) n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E)
    (hclosed : ∀ Φ : SimplexSurface (m + 1 + 1) n, ContDiff ℝ 1 Φ.map →
      (∀ u, Φ.map u ∈ E) → integralOverSimplex (extDeriv ω) Φ = 0) :
    ∃ η : KForm m n, (∀ i, ContDiffOn ℝ 1 (η.coeff i) E) ∧
      ∀ Φ : SimplexSurface (m + 1) n, ContDiff ℝ 1 Φ.map → (∀ u, Φ.map u ∈ E) →
        integralOverSimplex ω Φ = integralOverSimplex (extDeriv η) Φ := by
  obtain ⟨η, hηsmooth, hηalt⟩ :=
    ch10_primitive_of_closed m n E hE hconv ω hω (ch10_closed_pointwise m n E hE ω hω hclosed)
  refine ⟨η, hηsmooth, ?_⟩
  intro Φ _ hmem
  exact ch10_integral_alternation (m + 1) n E ω (extDeriv η)
    (fun x hx i => (hηalt x hx i).symm) Φ fun u _ => hmem u

