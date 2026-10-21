-- Prove2me | solution 1 for RobustPower.SimplexGap.lemma_2_4_not_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:27:04.835751+00:00
-- url     : https://prove2.me/submissions/dca97335-5d70-4743-bc18-8ecda41dd867

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

set_option autoImplicit false

open RobustPower.SimplexGap

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ¬ RobustPower.StochGap.IsSymmetric (cornerSimplex n) := by
  rintro ⟨u, -, hsym⟩
  -- reflection: x ∈ P → 2u - x ∈ P
  have hrefl : ∀ x ∈ cornerSimplex n, 2 • u - x ∈ cornerSimplex n := by
    intro x hx
    have h := (hsym (x - u)).1 (by simpa using hx)
    have e : u - (x - u) = 2 • u - x := by
      ext i; simp; ring
    rwa [e] at h
  have h0 : (0 : Fin n → ℝ) ∈ cornerSimplex n := by
    refine ⟨by simp, le_refl _⟩
  have h2u := hrefl 0 h0
  have hsum : ∑ i, (2 • u - (0 : Fin n → ℝ)) i ≤ 1 := h2u.1
  have hi : ∀ i : Fin n, 1 ≤ 2 * u i := by
    intro i
    have hx : (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ cornerSimplex n := by
      refine ⟨?_, ?_⟩
      · simp
      · intro j; by_cases h : j = i <;> simp [Pi.single_apply, h]
    have := (hrefl _ hx).2 i
    simp at this
    linarith
  have hge : (n : ℝ) ≤ ∑ i, (2 • u - (0 : Fin n → ℝ)) i := by
    have : ∑ _i : Fin n, (1 : ℝ) ≤ ∑ i, (2 • u - (0 : Fin n → ℝ)) i :=
      Finset.sum_le_sum (fun i _ => by simpa using hi i)
    simpa using this
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith
