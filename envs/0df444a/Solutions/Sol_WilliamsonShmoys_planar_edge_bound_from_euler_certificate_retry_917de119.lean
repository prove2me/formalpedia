-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_euler_certificate_retry_917de119
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T02:35:17.980356+00:00
-- url     : https://prove2.me/submissions/a385986a-2485-44b9-8c4c-c85de91f8100

import Mathlib

set_option autoImplicit false

theorem solution
    {V F : Type} [Fintype V] [Fintype F]
    (G : SimpleGraph V)
    (boundaryLength : F → ℕ)
    (hFace : ∀ f : F, 3 <= boundaryLength f)
    (hIncidence : Finset.sum Finset.univ boundaryLength = 2 * G.edgeSet.ncard)
    (hEuler : Fintype.card V + Fintype.card F = G.edgeSet.ncard + 2) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have h := Finset.card_nsmul_le_sum (Finset.univ : Finset F) boundaryLength 3 (fun f _ => hFace f)
  simp only [Finset.card_univ, smul_eq_mul] at h
  omega
