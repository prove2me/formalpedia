-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph_c61b3391
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:24:30.153664+00:00
-- url     : https://prove2.me/submissions/65014361-361e-411b-875b-ad5d417bce5a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono_for_exists_edge_maximal_planar_supergraph_c61b3391
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_hereditary_4121e569_c371_49f5_94ae_97541a850462

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V,
          H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  exact WilliamsonShmoys.exists_maximal_supergraph_of_finite_hereditary_4121e569_c371_49f5_94ae_97541a850462
    (P := WilliamsonShmoys.HasPlanarDrawingOn)
    (by
      intro A B hAB hB
      exact WilliamsonShmoys.hasPlanarDrawingOn_mono_for_exists_edge_maximal_planar_supergraph_c61b3391 hAB hB)
    G hG