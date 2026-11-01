-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_edge_count__p2m_7d22c919_3efe_4469_8040_ed9baa851075_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:56:38.932+00:00
-- url     : https://prove2.me/submissions/12f04cf9-0796-4aed-b656-121c589010a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_edge_maximal_drawable_extension__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
import Theorems.Thm_edge_maximal_drawable_has_euler_edge_count__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      N.edgeFinset ⊆ K.edgeFinset ∧
      K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨K, dK, hK, hNK, hmax⟩ :=
    exists_edge_maximal_drawable_extension__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
      N dN hN
  exact ⟨K, dK, hK, hNK,
    edge_maximal_drawable_has_euler_edge_count__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
      K dK hK hcard hmax⟩