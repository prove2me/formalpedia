-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_upper_bound__p2m_b64ef977_b4ef_4b2b_beae_4cc23cd005bf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:54:44.291782+00:00
-- url     : https://prove2.me/submissions/ab7c9690-98b4-46fe-bc73-aa1e3bf85470
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_2cd0a648_3850_4669_bbb5_b62598f0c8b2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_2cd0a648_3850_4669_bbb5_b62598f0c8b2_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn J) :
    J.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hHplanar, hmax, hmono⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2cd0a648_3850_4669_bbb5_b62598f0c8b2_a1
      J hcard hplanar
  have heq :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_2cd0a648_3850_4669_bbb5_b62598f0c8b2_a1
      H hcard hHplanar hmax
  omega