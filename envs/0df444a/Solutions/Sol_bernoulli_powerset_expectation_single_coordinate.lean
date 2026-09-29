-- Prove2me | solution 1 for bernoulli_powerset_expectation_single_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T20:52:06.376031+00:00
-- url     : https://prove2.me/submissions/d8a92554-91d4-40fc-ae3f-ed99666f9764

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_powerset_expectation_prod_factor
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

/-- `bernoulli_powerset_expectation_single_coordinate`.

**Single-coordinate marginal** of the Bernoulli powerset expectation: the
expectation of a statistic depending only on the inclusion of one fixed
coordinate `w` equals `p·g(1) + (1-p)·g(0)`. Derived from the product
factorization (independence) lemma by choosing the per-coordinate function to be
`g` at `w` and the constant `1` elsewhere; both the LHS product and the RHS
product then collapse to their single non-trivial factor. -/
theorem solution {n₁ n₂ : ℕ}
    (p : ℝ) (w : Fin n₁ × Fin n₂) (g : ℝ → ℝ) :
    bernoulliExpectation p (fun Omega => g (if w ∈ Omega then 1 else 0)) =
      p * g 1 + (1 - p) * g 0 := by
  classical
  have key := bernoulli_powerset_expectation_prod_factor (n₁ := n₁) (n₂ := n₂) p
    (fun w' => if w' = w then g else (fun _ => 1))
  have hL : (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        ∏ w' : Fin n₁ × Fin n₂,
          (if w' = w then g else (fun _ => (1:ℝ))) (if w' ∈ Omega then 1 else 0)) =
      (fun Omega => g (if w ∈ Omega then 1 else 0)) := by
    funext Omega
    rw [Finset.prod_eq_single w]
    · simp
    · intro b _ hb; simp [hb]
    · intro hb; exact absurd (Finset.mem_univ w) hb
  rw [hL] at key
  rw [key, Finset.prod_eq_single w]
  · simp
  · intro b _ hb; simp [hb]
  · intro hb; exact absurd (Finset.mem_univ w) hb
