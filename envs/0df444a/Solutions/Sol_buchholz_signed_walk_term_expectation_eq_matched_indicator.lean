-- Prove2me | solution 1 for buchholz_signed_walk_term_expectation_eq_matched_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T23:39:12.397169+00:00
-- url     : https://prove2.me/submissions/d619b759-c5dd-4804-8b64-1500b6504acd

import Theorems.Thm_E_sign_monomial
import Theorems.Thm_buchholz_walk_sign_monomial_eq_edge_multiplicity_product
import Definitions.Def_buchholz_matched_walk_contribution

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Section 2; Candès--Recht, Section 6.1,
Lemma 6.1, PDF p. 25.

Reduction: reindex the fixed walk's sign monomial by coordinate-edge
multiplicity, then apply the platform sign-cube orthogonality theorem
`E_sign_monomial`.
-/
theorem solution
    {n n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) :
    rademacherExpectation
        (fun eps => buchholzSignedWalkTerm Omega eps p X rows cols)
      = buchholzMatchedWalkContribution Omega p X rows cols := by
  classical
  let P : ℝ := buchholzWalkProduct Omega p X rows cols
  let mult : (Fin n1 × Fin n2) → ℕ := fun c => buchholzEdgeMultiplicity rows cols c
  have hsign :
      ∀ eps : Finset (Fin n1 × Fin n2),
        buchholzWalkSignMonomial eps rows cols =
          ∏ c : Fin n1 × Fin n2,
            (if c ∈ eps then (1 : ℝ) else -1) ^ mult c := by
    intro eps
    calc
      buchholzWalkSignMonomial eps rows cols
          = ∏ c : Fin n1 × Fin n2,
              rademacherSign eps c.1 c.2 ^
                buchholzEdgeMultiplicity rows cols c := by
            exact buchholz_walk_sign_monomial_eq_edge_multiplicity_product eps rows cols
      _ = ∏ c : Fin n1 × Fin n2,
              (if c ∈ eps then (1 : ℝ) else -1) ^ mult c := by
            simp [rademacherSign, mult]
  unfold rademacherExpectation rademacherObservationWeight
  unfold buchholzSignedWalkTerm
  simp only [P, mult]
  calc
    ∑ eps : Finset (Fin n1 × Fin n2),
        ((1 : ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) *
          (buchholzWalkProduct Omega p X rows cols *
            buchholzWalkSignMonomial eps rows cols)
        =
      ∑ eps : Finset (Fin n1 × Fin n2),
        buchholzWalkProduct Omega p X rows cols *
          (((1 : ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) *
            ∏ c : Fin n1 × Fin n2,
              (if c ∈ eps then (1 : ℝ) else -1) ^ mult c) := by
        apply Finset.sum_congr rfl
        intro eps _heps
        rw [hsign eps]
        ring
    _ =
      buchholzWalkProduct Omega p X rows cols *
        (∑ eps : Finset (Fin n1 × Fin n2),
          ((1 : ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) *
            ∏ c : Fin n1 × Fin n2,
              (if c ∈ eps then (1 : ℝ) else -1) ^ mult c) := by
        rw [Finset.mul_sum]
    _ =
      buchholzWalkProduct Omega p X rows cols *
        (((1 : ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) *
          ∑ eps : Finset (Fin n1 × Fin n2),
            ∏ c : Fin n1 × Fin n2,
              (if c ∈ eps then (1 : ℝ) else -1) ^ mult c) := by
        congr 1
        rw [Finset.mul_sum]
    _ =
      buchholzWalkProduct Omega p X rows cols *
        (if (∀ c : Fin n1 × Fin n2, Even (mult c)) then 1 else 0) := by
        rw [E_sign_monomial mult]
    _ =
      buchholzMatchedWalkContribution Omega p X rows cols := by
        unfold buchholzMatchedWalkContribution buchholzWalkMatched
        by_cases h : ∀ c : Fin n1 × Fin n2,
            Even (buchholzEdgeMultiplicity rows cols c)
        · simp [h, mult]
        · simp [h, mult]
