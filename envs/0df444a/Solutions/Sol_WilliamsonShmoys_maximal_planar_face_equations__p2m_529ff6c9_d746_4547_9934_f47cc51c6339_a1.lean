-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_equations__p2m_529ff6c9_d746_4547_9934_f47cc51c6339_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:37.433123+00:00
-- url     : https://prove2.me/submissions/e036b2c9-0992-4d79-b147-5fd5f7a2f5c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5ab9b52f_fdb8_4eff_9a4e_c2dd12c7a0d0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hE := WilliamsonShmoys.maximal_planar_edge_count__p2m_5ab9b52f_fdb8_4eff_9a4e_c2dd12c7a0d0_a1
    L hDraw hMax hV
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega