-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper_bound_c06a69a3_ca91_45ac_86f5_c61df4ae7c99
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T14:04:21.972721+00:00
-- url     : https://prove2.me/submissions/fd7bd3ff-6aba-4630-9e88-37a605ee6de0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨K, hLK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce L hL
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce
      K hK hmax hCard
  have hcount : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    omega
  calc
    L.edgeSet.ncard <= K.edgeSet.ncard :=
      Set.ncard_mono (SimpleGraph.edgeSet_subset_edgeSet.mpr hLK)
    _ = 3 * Fintype.card V - 6 := hcount