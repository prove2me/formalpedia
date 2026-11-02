-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_077d3f0d_ff79_48f3_bde0_954cbd7dcf68_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:00:55.659129+00:00
-- url     : https://prove2.me/submissions/bb294da4-a529-4d19-b505-7d95e9000929
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    exists J : SimpleGraph V, And (HasPlanarDrawingOn J)
      (And (H <= J) (J.edgeFinset.card = 3 * Fintype.card V - 6)) := by
  classical
  letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  obtain ⟨J, hJ, hHJ, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
      H hH hcard
  refine ⟨J, hJ, hHJ, ?_⟩
  exact WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
    J hJ hmax hcard