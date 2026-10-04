-- Prove2me | solution 1 for VanderbeiLP.Simplex.lex_pivot_increases_perturbed_objective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-03T20:58:42.264983+00:00
-- url     : https://prove2.me/submissions/cd545ee8-fd9d-4cf7-ae89-6ebc0793972d

import Theorems.Thm_VanderbeiLP_Simplex_lex_pivot_perturbed_objective_basis_exchange

open VanderbeiLP.Simplex

theorem solution {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (D₀ D D' : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hpos : ∀ i ∈ D.B, toLex (0 : Fin (m + 1) → ℝ) <
      toLex (Dictionary.lexRow D₀ D b i))
    (hpivot : Dictionary.IsLexPivot D₀ b c D D') :
    toLex (∑ i ∈ D.B, extCost c i • Dictionary.lexRow D₀ D b i) <
    toLex (∑ i ∈ D'.B, extCost c i • Dictionary.lexRow D₀ D' b i) := by
  classical
  rcases hpivot with ⟨k, l, henter, hleave, hB⟩
  let scale : ℝ := D.cbar c k / D.abar l k
  let row := Dictionary.lexRow D₀ D b l
  let oldObj := ∑ i ∈ D.B, extCost c i • Dictionary.lexRow D₀ D b i
  let delta := scale • row
  have hscale : Pi.Lex (· < ·) (· < ·) (0 : Fin (m + 1) → ℝ) delta := by
    have hrow := hpos l hleave.1
    change Pi.Lex (· < ·) (· < ·) (0 : Fin (m + 1) → ℝ) row at hrow
    rcases hrow with ⟨j, hj, hlt⟩
    refine ⟨j, ?_, ?_⟩
    · intro i hij
      have hz := hj i hij
      change 0 = row i at hz
      simp [delta, scale, row, ← hz]
    · have hcoef : 0 < scale := div_pos henter.2 hleave.2.1
      simpa [delta, scale, row] using (mul_pos hcoef hlt)
  have hidentity := lex_pivot_perturbed_objective_basis_exchange D₀ D D' b c k l
    henter hleave hB
  rw [hidentity]
  change Pi.Lex (· < ·) (· < ·) oldObj (oldObj + delta)
  rcases hscale with ⟨j, hj, hlt⟩
  refine ⟨j, ?_, ?_⟩
  · intro i hij
    have hz := hj i hij
    change 0 = delta i at hz
    simp [hz]
  · exact lt_add_of_pos_right _ hlt