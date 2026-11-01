-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_augmentation__p2m_064c0857_cede_4cc8_908c_7ab641b39ae5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:56:44.381051+00:00
-- url     : https://prove2.me/submissions/d333bad0-fc3e-4779-9c75-f91ef3d36013
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_60570168_fc59_4828_82d8_84f6b859c6a0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_60570168_fc59_4828_82d8_84f6b859c6a0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      L <= K ∧ HasPlanarDrawingOn K ∧
        (letI : DecidableRel K.Adj := dK;
          K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨K, hLK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_60570168_fc59_4828_82d8_84f6b859c6a0_a1
      L hL
  let dK : DecidableRel K.Adj := Classical.decRel _
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_60570168_fc59_4828_82d8_84f6b859c6a0_a1
      K dK hK hcard hmax
  exact ⟨K, dK, hLK, hK, hcount⟩