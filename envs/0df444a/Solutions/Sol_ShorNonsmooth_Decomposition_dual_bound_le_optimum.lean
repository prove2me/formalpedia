-- Prove2me | solution 1 for ShorNonsmooth.Decomposition.dual_bound_le_optimum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:30:00.448297+00:00
-- url     : https://prove2.me/submissions/75add3da-d815-4d47-a06d-35896969aa24

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_PenaltyDual

open ShorNonsmooth.Decomposition in
theorem solution {N m : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (hX : IsCompact X)
    (f₀ : EuclideanSpace ℝ (Fin N) → ℝ) (f : Fin m → EuclideanSpace ℝ (Fin N) → ℝ)
    (hmin : ∀ u : Fin m → ℝ, (∀ i, 0 ≤ u i) →
      ∃ x ∈ X, ∀ x' ∈ X, f₀ x + ∑ i, u i * f i x ≤ f₀ x' + ∑ i, u i * f i x')
    (fstar : ℝ) (hfstar : IsLeast (f₀ '' (X ∩ feasibleSet f)) fstar)
    (Q : ℝ) (hQ : IsGreatest (dualFn X f₀ f '' {u | ∀ i, 0 ≤ u i}) Q) :
    Q ≤ fstar := by
  obtain ⟨⟨u, hu, rfl⟩, -⟩ := hQ
  obtain ⟨⟨xs, ⟨hxsX, hxsF⟩, rfl⟩, -⟩ := hfstar
  obtain ⟨x0, hx0X, hx0⟩ := hmin u hu
  have hbdd : BddBelow ((fun x => f₀ x + ∑ i, u i * f i x) '' X) := by
    refine ⟨f₀ x0 + ∑ i, u i * f i x0, ?_⟩
    rintro _ ⟨x', hx', rfl⟩
    exact hx0 x' hx'
  have h1 : dualFn X f₀ f u ≤ f₀ xs + ∑ i, u i * f i xs :=
    csInf_le hbdd ⟨xs, hxsX, rfl⟩
  have h2 : ∑ i, u i * f i xs ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hu i) (hxsF i)
  linarith
