-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_bound__p2m_09ee00d6_d6e0_4e98_aab0_c4cdc0b16fb7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:14:14.505273+00:00
-- url     : https://prove2.me/submissions/0578de67-8397-496f-868f-713a4219dd2f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdraw : HasPlanarDrawingOn L) :
    letI : forall G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    exists M : SimpleGraph V,
      L.edgeFinset ⊆ M.edgeFinset /\
      HasPlanarDrawingOn M /\
      3 * Fintype.card V - 6 <= M.edgeFinset.card := by
  classical
  letI : forall G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  obtain ⟨M, hsub, hdrawM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
      L hdraw
  have hbound :=
    WilliamsonShmoys.maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
      M hcard hdrawM hmax
  exact ⟨M, hsub, hdrawM, hbound⟩