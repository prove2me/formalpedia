-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_connected__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:22:36.761485+00:00
-- url     : https://prove2.me/submissions/b394f070-388f-43ad-9ed8-18565c7c77cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_strict_drawable_extension__p2m_028b57dc_ebab_41ef_892a_6b94678daa69_a3
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ H : SimpleGraph V,
      M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ M) :
    M.Connected := by
  classical
  by_contra hconn
  obtain ⟨H, hMH, hH, hnotHM⟩ :=
    WilliamsonShmoys.planar_disconnected_has_strict_drawable_extension__p2m_028b57dc_ebab_41ef_892a_6b94678daa69_a3
      M hn hM hconn
  exact hnotHM (hmax H hMH hH)