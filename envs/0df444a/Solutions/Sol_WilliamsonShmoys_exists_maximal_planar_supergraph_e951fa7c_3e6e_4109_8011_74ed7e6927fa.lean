-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:41:45.478556+00:00
-- url     : https://prove2.me/submissions/b80a8b0a-b0b8-46c4-9f01-2500f370a7a0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_simple_graphs_on_fintype
import Theorems.Thm_finite_partial_order_exists_maximal

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V,
      LE.le W X ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      (∀ Y : SimpleGraph V,
        LE.le X Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) := by
  classical
  let s : Set (SimpleGraph V) :=
    {X | LE.le W X ∧ WilliamsonShmoys.HasPlanarDrawingOn X}
  have hs : s.Nonempty := ⟨W, le_rfl, hW⟩
  letI : Finite (SimpleGraph V) := finite_simple_graphs_on_fintype (V := V)
  obtain ⟨X, hXs, hmax⟩ :=
    finite_partial_order_exists_maximal (α := SimpleGraph V) s hs
  refine ⟨X, hXs.1, hXs.2, ?_⟩
  intro Y hXY hY
  have hYs : Y ∈ s := ⟨le_trans hXs.1 hXY, hY⟩
  exact hmax Y hYs hXY