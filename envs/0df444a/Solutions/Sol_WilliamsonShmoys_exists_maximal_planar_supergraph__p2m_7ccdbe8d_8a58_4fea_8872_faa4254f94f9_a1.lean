-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:18.212276+00:00
-- url     : https://prove2.me/submissions/2f434bc1-f9f1-4569-8302-bdd685545cf0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J →
        J.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hnonempty : candidates.Nonempty := by
    refine ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ K, le_rfl, hDraw⟩⟩
  obtain ⟨H, hH, hmax⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeSet.ncard) hnonempty
  refine ⟨H, (Finset.mem_filter.mp hH).2.1, (Finset.mem_filter.mp hH).2.2, ?_⟩
  intro J hKJ hJDraw
  apply hmax J
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ J, hKJ, hJDraw⟩