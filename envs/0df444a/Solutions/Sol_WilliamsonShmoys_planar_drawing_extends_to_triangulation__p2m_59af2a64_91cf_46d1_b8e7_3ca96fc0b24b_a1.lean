-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_59af2a64_91cf_46d1_b8e7_3ca96fc0b24b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:31:05.962734+00:00
-- url     : https://prove2.me/submissions/514b5aae-0f78-4f99-88a0-a49202a3c501
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U ∧
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) ∧
      (letI : DecidableRel U.Adj := dU
       U.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨U, dU, hU, hTU, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
      T dT hT
  have hcount :=
    WilliamsonShmoys.edge_count_of_edge_maximal_planar__p2m_6b272625_9d5c_443e_9411_b56416706ef1_a1
      U dU hU hmax hcard
  exact ⟨U, dU, hU, hTU, hcount⟩