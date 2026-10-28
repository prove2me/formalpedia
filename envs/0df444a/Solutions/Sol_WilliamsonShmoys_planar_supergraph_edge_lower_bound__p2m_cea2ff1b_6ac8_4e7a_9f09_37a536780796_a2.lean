-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_cea2ff1b_6ac8_4e7a_9f09_37a536780796_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:53:39.988288+00:00
-- url     : https://prove2.me/submissions/53ee7d5b-df2a-4273-ae7b-f0a616d8f013
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_supergraph__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      R ≤ T ∧
      3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  obtain ⟨T, hT, hRT, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1
      R hR
  exact ⟨T, hT, hRT,
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1
      T hT hmax hCard⟩