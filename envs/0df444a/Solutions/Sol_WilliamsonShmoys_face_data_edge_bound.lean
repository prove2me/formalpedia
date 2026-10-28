-- Prove2me | solution 1 for WilliamsonShmoys.face_data_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:20:28.687289+00:00
-- url     : https://prove2.me/submissions/cdb096a9-052a-410f-b9e6-1bcaeacf03d3

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (J : SimpleGraph V)
    (hData : ∃ F : ℕ, Fintype.card V + F = J.edgeSet.ncard + 2 ∧
      3 * F ≤ 2 * J.edgeSet.ncard) :
    J.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨F, hEuler, hSides⟩ := hData
  omega