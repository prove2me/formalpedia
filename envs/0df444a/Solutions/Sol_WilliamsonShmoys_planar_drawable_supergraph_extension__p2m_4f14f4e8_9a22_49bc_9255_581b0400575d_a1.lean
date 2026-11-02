-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_supergraph_extension__p2m_4f14f4e8_9a22_49bc_9255_581b0400575d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:40:18.195211+00:00
-- url     : https://prove2.me/submissions/0d76d6f0-5819-4206-acdf-637b490c65eb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, HasPlanarDrawingOn N ∧ M ≤ N ∧
      ∀ K : SimpleGraph V, HasPlanarDrawingOn K → N ≤ K → K ≤ N → N = K := by
  refine ⟨M, hM, le_rfl, ?_⟩
  intro K _ hMK hKM
  exact le_antisymm hMK hKM