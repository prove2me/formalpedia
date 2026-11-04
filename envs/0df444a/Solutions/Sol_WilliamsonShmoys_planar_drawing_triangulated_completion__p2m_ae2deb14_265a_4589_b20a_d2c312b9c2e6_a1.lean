-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_completion__p2m_ae2deb14_265a_4589_b20a_d2c312b9c2e6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:02:43.084198+00:00
-- url     : https://prove2.me/submissions/cfb0655c-5995-43ed-8f0d-763e8bccc67e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulated_edge_count__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn G) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : ∀ H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
  obtain ⟨H, hGH, hHdrawing, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1 G hdrawing
  exact ⟨H, hGH, hHdrawing,
    WilliamsonShmoys.maximal_planar_drawing_has_triangulated_edge_count__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1 H hcard hHdrawing hmax⟩