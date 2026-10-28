-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_drawing_edge_count_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:49:36.645993+00:00
-- url     : https://prove2.me/submissions/f680dfb7-399c-4c9e-a14b-aa91f755e1fe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph_repair_3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair_3
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  classical
  obtain ⟨L, hKL, hL, hLmax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_supergraph_repair_3 K hK
  have hcount := WilliamsonShmoys.maximal_planar_edge_count_repair_3 L hL hcard hLmax
  have hLK : L = K := hmax L hKL hL
  rw [hLK] at hcount
  exact le_of_eq hcount