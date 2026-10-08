-- Prove2me | solution 1 for ShadowTomography.ClassicalLB.acceptance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:23:49.43655+00:00
-- url     : https://prove2.me/submissions/c3ebbae4-2031-462d-bd09-9c0c4d5e26c9

import Mathlib
import Definitions.Def_ShadowTomography_ClassicalLB_biasedDist

open ShadowTomography.ClassicalLB in
theorem solution (N : ℕ) (S : Finset (Fin N)) (ε : ℝ)
    (hhalf : 2 * S.card = N) (hne : 1 ≤ S.card)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 6) :
    ∑ x ∈ S, biasedDist N S ε x = 1 / 2 + 3 * ε := by
  have h : ∀ x ∈ S, biasedDist N S ε x = (1 / 2 + 3 * ε) / (N / 2 : ℝ) := by
    intro x hx
    simp [biasedDist, hx]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  have hN : (N : ℝ) = 2 * (S.card : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hhalf
    push_cast at this; linarith
  have hc : (S.card : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hne
    linarith
  rw [hN]
  field_simp
