-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_of_sparse
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:25:52.897032+00:00
-- url     : https://prove2.me/submissions/a9df74c2-00e2-4a09-8770-d4e0ecfcb801
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_395ae7cf

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hsparse : H.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ G : SimpleGraph V, H ≤ G ∧ G ≠ H ∧ WilliamsonShmoys.HasPlanarDrawingOn G := by
  obtain ⟨G, hHG, hplanar, hcard⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_supergraph_395ae7cf H hV hH
  refine ⟨G, hHG, ?_, hplanar⟩
  intro hEq
  subst G
  rw [hcard] at hsparse
  omega
