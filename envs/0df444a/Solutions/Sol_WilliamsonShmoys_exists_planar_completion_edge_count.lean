-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_completion_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:33:17.116767+00:00
-- url     : https://prove2.me/submissions/e77a77fa-c004-4025-ab9f-82e004d33278
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_completion_repair_271d2eb8_0883_4afb_88e9_925bc682e12d
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair_271d2eb8_0883_4afb_88e9_925bc682e12d

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_completion_repair_271d2eb8_0883_4afb_88e9_925bc682e12d
      H hHplanar
  exact ⟨K, hHK, hKplanar,
    WilliamsonShmoys.maximal_planar_edge_count_repair_271d2eb8_0883_4afb_88e9_925bc682e12d
      K hV hKplanar hKmax⟩