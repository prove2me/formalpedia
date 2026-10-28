-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_has_connected_supergraph_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:16:37.3913+00:00
-- url     : https://prove2.me/submissions/210bf1fc-9885-471c-9b98-5ef213edb45d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_connected_extension_b575eb0b_092c_4d6e_a44b_f1a402a11573
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_drawable_edge_extension_for_connected_extension_b575eb0b_092c_4d6e_a44b_f1a402a11573

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ M : SimpleGraph V,
      J ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.Connected := by
  obtain ⟨M, hJM, hDrawM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_connected_extension_b575eb0b_092c_4d6e_a44b_f1a402a11573 J hDraw
  refine ⟨M, hJM, hDrawM, ?_⟩
  by_contra hNotConnected
  obtain ⟨N, hMN, hNeq, hDrawN⟩ :=
    WilliamsonShmoys.planar_disconnected_has_drawable_edge_extension_for_connected_extension_b575eb0b_092c_4d6e_a44b_f1a402a11573
      M hDrawM hNotConnected
  exact hNeq (Eq.symm (hmax N hMN hDrawN))