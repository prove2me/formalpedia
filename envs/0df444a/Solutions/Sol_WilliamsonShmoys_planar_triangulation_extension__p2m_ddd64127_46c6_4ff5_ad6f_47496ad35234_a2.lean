-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_ddd64127_46c6_4ff5_ad6f_47496ad35234_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:45:36.371991+00:00
-- url     : https://prove2.me/submissions/3cb4b04a-cadd-4a69-a95d-281e47d529aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a3
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      Exists fun dK : DecidableRel K.Adj =>
        And (H.edgeFinset ⊆ K.edgeFinset)
          (K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  rcases WilliamsonShmoys.planar_maximal_supergraph__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a3
      H dH hH hcard with ⟨K, hK⟩
  rcases hK with ⟨dK, hKD⟩
  rcases hKD with ⟨hsub, hrest⟩
  rcases hrest with ⟨hplanar, hmax⟩
  have hcount := WilliamsonShmoys.maximal_planar_edge_count__p2m_193b553a_1cdb_4a08_8993_1d661c78bfd1_a3
      K dK hplanar hcard hmax
  exact ⟨K, ⟨dK, ⟨hsub, hcount⟩⟩⟩