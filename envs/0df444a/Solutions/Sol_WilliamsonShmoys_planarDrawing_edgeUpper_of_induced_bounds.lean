-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_edgeUpper_of_induced_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:11:06.527924+00:00
-- url     : https://prove2.me/submissions/8c0b5bbc-f2d6-410f-a53b-43bd5df9e544

import Mathlib
import Theorems.Thm_WilliamsonShmoys_edgeUpper_of_connected_partition
import Theorems.Thm_WilliamsonShmoys_exists_connected_component_partition

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (connectedInducedBound : ∀ (S : Finset V),
      (G.induce (↑S : Set V)).Connected →
      3 ≤ Fintype.card S →
      (G.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card S)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨C, hcover, hdisjoint, hconnected, hadj⟩ :=
    WilliamsonShmoys.exists_connected_component_partition G
  exact WilliamsonShmoys.edgeUpper_of_connected_partition
    G C connectedInducedBound hV hcover hdisjoint hconnected hadj