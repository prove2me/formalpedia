-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_component_partition
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:00:49.500979+00:00
-- url     : https://prove2.me/submissions/af0106aa-2667-400f-a51e-9d26c01e3270

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_component_partition
import Theorems.Thm_WilliamsonShmoys_planar_drawing_induce

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ C : Finset (Finset V),
      (∀ S ∈ C, S.Nonempty) ∧
      (∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S) ∧
      (∀ ⦃u v : V⦄, H.Adj u v → ∃ S ∈ C, u ∈ S ∧ v ∈ S) ∧
      (∀ S ∈ C, (H.induce (↑S : Set V)).Connected) ∧
      (∀ S ∈ C, WilliamsonShmoys.HasPlanarDrawingOn
        (H.induce (↑S : Set V))) := by
  obtain ⟨C, hnonempty, hcover, hedge, hconnected⟩ :=
    WilliamsonShmoys.finite_component_partition H
  refine ⟨C, hnonempty, hcover, hedge, hconnected, ?_⟩
  intro S hS
  exact WilliamsonShmoys.planar_drawing_induce H hH S