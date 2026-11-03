-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_fd310935_5091_4856_a806_c268ac2a777f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:26:54.279676+00:00
-- url     : https://prove2.me/submissions/2d2cbebc-c729-4514-a869-4f1a7578b88f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_1869d2b3_4acb_4df1_b926_664515403053_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_1869d2b3_4acb_4df1_b926_664515403053_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨K, hHK, hKdraw, hKmax, hcardHK⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_1869d2b3_4acb_4df1_b926_664515403053_a2
      H hdraw
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hK :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_1869d2b3_4acb_4df1_b926_664515403053_a2
      K hcard hKdraw hKmax
  omega