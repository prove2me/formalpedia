-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_completion__p2m_7eac73df_a948_4c33_96ae_30ffe17dadaf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:16:48.842093+00:00
-- url     : https://prove2.me/submissions/605eeaba-e88f-43bb-beb7-4afd466fb554

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_completion__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_has_euler_edge_count__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 ≤ Fintype.card V) :
    ∃ M' : SimpleGraph V, M ≤ M' ∧ WilliamsonShmoys.HasPlanarDrawingOn M' ∧
      3 * Fintype.card V = M'.edgeSet.ncard + 6 := by
  obtain ⟨M', hsub, hM'planar, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_completion__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1 M hplanar
  refine ⟨M', hsub, hM'planar, ?_⟩
  exact WilliamsonShmoys.edge_maximal_planar_has_euler_edge_count__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1 M' hM'planar hcard hmax
