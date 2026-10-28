-- Prove2me | solution 2 for WilliamsonShmoys.face_census_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:31:48.082335+00:00
-- url     : https://prove2.me/submissions/349bb609-759f-4891-9bbf-b0404f2a9bda

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : ℕ)
    (degree : Fin f → ℕ)
    (hn : 3 ≤ n)
    (hEuler : n + f = m + 2)
    (hDegreeSum : (∑ i : Fin f, degree i) = 2 * m)
    (hFaceDegree : ∀ i, 3 ≤ degree i) :
    m ≤ 3 * n - 6 := by
  have h : ∑ _i : Fin f, 3 ≤ ∑ i : Fin f, degree i :=
    Finset.sum_le_sum (fun i _ => hFaceDegree i)
  simp at h
  omega
