-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound_78919b52_de37_4426_ade1_0aaa5522d1e4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:31:10.329333+00:00
-- url     : https://prove2.me/submissions/beb22c1b-953e-46f5-a6c4-7ba4d2642b0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_augmentation_78919b52_de37_4426_ade1_0aaa5522d1e4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_78919b52_de37_4426_ade1_0aaa5522d1e4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_augmentation_78919b52_de37_4426_ade1_0aaa5522d1e4
      K hK hCard
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_edge_bound_78919b52_de37_4426_ade1_0aaa5522d1e4
      L hL hMax hCard⟩