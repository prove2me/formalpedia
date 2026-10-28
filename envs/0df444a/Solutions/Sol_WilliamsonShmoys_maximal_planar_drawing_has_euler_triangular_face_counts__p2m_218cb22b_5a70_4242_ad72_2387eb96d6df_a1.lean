-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_euler_triangular_face_counts__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:54:32.315501+00:00
-- url     : https://prove2.me/submissions/9cf45e5e-5973-43b1-9a73-119fe0bc88a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V) :
    ∃ f : ℕ, f + Fintype.card V = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hEdges := WilliamsonShmoys.maximal_planar_drawing_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3
    L hDraw hCard (fun M hLM hM => le_of_eq (hMax M hLM hM))
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega