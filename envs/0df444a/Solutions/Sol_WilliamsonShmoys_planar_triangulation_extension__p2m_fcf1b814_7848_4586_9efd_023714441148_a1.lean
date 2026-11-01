-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_fcf1b814_7848_4586_9efd_023714441148_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:50:17.47318+00:00
-- url     : https://prove2.me/submissions/05272fac-88d0-4784-a664-c699a85615a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_supergraph__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_has_3n_minus_6_edges__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U ∧
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) ∧
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       U.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨U, dU, hU, hTU, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_maximal_supergraph__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1
      T dT hT hn
  have hcard :=
    WilliamsonShmoys.edge_maximal_planar_drawing_has_3n_minus_6_edges__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1
      U dU hU hn hmax
  exact ⟨U, dU, hU, hTU, hcard⟩