-- Prove2me | solution 1 for WilliamsonShmoys.face_census_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:31:07.030722+00:00
-- url     : https://prove2.me/submissions/e17c08af-3728-4919-a4e0-9528235c1b46

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
  have h : (∑ _i : Fin f, 3) ≤ ∑ i : Fin f, degree i := Finset.sum_le_sum fun i _ => hFaceDegree i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega
