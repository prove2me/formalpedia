-- Prove2me | solution 1 for WilliamsonShmoys.drawable_connected_supergraph__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T00:28:08.853247+00:00
-- url     : https://prove2.me/submissions/5ccdee3d-935b-49da-b346-9ad48b1a7efe

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_exists

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V,
      M ≤ G ∧ G.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn G := by
  exact WilliamsonShmoys.planar_drawing_connected_extension_exists M hcard hM
