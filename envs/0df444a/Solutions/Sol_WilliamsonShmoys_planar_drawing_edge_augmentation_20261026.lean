-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_augmentation_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:32:52.521365+00:00
-- url     : https://prove2.me/submissions/1faa16e6-169c-43fd-994e-549b15409bf7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_20261026
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_20261026

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hbelow : M.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ N ≠ M ∧ WilliamsonShmoys.HasPlanarDrawingOn N := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_20261026 M hM
  have hNcard :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_20261026 N hV hN hmax
  have hneq : N ≠ M := by
    intro hEq
    subst N
    omega
  exact ⟨N, hMN, hneq, hN⟩