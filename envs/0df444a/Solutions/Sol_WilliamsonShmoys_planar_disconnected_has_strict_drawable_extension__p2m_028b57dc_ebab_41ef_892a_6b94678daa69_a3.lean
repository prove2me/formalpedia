-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_has_strict_drawable_extension__p2m_028b57dc_ebab_41ef_892a_6b94678daa69_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:44:30.250049+00:00
-- url     : https://prove2.me/submissions/0726b576-cab3-4786-b8e7-e20e6394e919
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_separated_pair__p2m_46cfe7ce_b627_4e5a_9d08_1eab5cbb77ec_a2
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_components__p2m_46cfe7ce_b627_4e5a_9d08_1eab5cbb77ec_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hdis : ¬ M.Connected) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ¬ H ≤ M := by
  obtain ⟨u, v, hnotReach, hnotAdj⟩ :=
    WilliamsonShmoys.planar_disconnected_has_separated_pair__p2m_46cfe7ce_b627_4e5a_9d08_1eab5cbb77ec_a2
      M hn hdis
  obtain ⟨H, hle, hadj, hdraw⟩ :=
    WilliamsonShmoys.planar_add_edge_between_components__p2m_46cfe7ce_b627_4e5a_9d08_1eab5cbb77ec_a2
      M hM hnotReach
  refine ⟨H, hle, hdraw, ?_⟩
  intro hHM
  exact hnotAdj (hHM hadj)