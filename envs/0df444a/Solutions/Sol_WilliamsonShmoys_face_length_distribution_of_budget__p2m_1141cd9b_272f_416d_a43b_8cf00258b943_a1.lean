-- Prove2me | solution 1 for WilliamsonShmoys.face_length_distribution_of_budget__p2m_1141cd9b_272f_416d_a43b_8cf00258b943_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:03.254791+00:00
-- url     : https://prove2.me/submissions/3b8a7b52-f7f7-4c70-86cd-14bf035820c9

import Mathlib

set_option autoImplicit false

theorem solution
    (f total : Nat)
    (hf : 0 < f)
    (hBudget : 3 * f ≤ total) :
    ∃ faceLength : Fin f → Nat,
      (∑ i : Fin f, faceLength i) = total ∧
      ∀ i : Fin f, 3 ≤ faceLength i := by
  cases f with
  | zero =>
      omega
  | succ n =>
      have hBudget' : 3 * n + 3 ≤ total := by
        omega
      have hFirst : 3 ≤ total - 3 * n := by
        omega
      refine ⟨Fin.cases (total - 3 * n) (fun _ => 3), ?_, ?_⟩
      · simp [Fin.sum_univ_succ]
        omega
      · intro i
        refine Fin.cases ?_ (fun _ => ?_) i
        · exact hFirst
        · simp