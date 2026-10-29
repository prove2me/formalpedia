-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_face_count_certificate__p2m_dd6d4a28_ff1c_4910_81ae_1b1a3100063c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:35:29.155713+00:00
-- url     : https://prove2.me/submissions/8612f68c-a011-4529-b800-3d12af4361f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4d9c8971_4afd_47f0_9ee2_860519fd763e_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hMax : ∀ u v, u ≠ v → ¬ T.Adj u v →
      ¬ ∃ U : SimpleGraph V,
        (∀ x y, T.Adj x y → U.Adj x y) ∧
        HasPlanarDrawingOn U ∧ U.Adj u v) :
    ∃ f : Nat,
      Fintype.card V + f = T.edgeSet.ncard + 2 ∧
      3 * f = 2 * T.edgeSet.ncard := by
  have hEdges := WilliamsonShmoys.maximal_planar_edge_count__p2m_4d9c8971_4afd_47f0_9ee2_860519fd763e_a1
    T hCard hT hMax
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega