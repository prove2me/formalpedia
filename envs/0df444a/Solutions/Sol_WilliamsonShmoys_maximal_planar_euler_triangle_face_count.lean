-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_triangle_face_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:14:56.173399+00:00
-- url     : https://prove2.me/submissions/f775a84f-8059-4b28-92dd-6b260d25129d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_d51190b1_8a07_4935_b1e8_3fdecb95c1b0

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  have hEdges := WilliamsonShmoys.maximal_planar_edge_count_d51190b1_8a07_4935_b1e8_3fdecb95c1b0 K hK hMax hCard
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega