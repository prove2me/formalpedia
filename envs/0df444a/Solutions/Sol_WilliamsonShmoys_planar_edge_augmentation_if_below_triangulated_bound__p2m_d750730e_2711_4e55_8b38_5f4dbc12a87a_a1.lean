-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_if_below_triangulated_bound__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:06:14.605731+00:00
-- url     : https://prove2.me/submissions/b6c9f94c-732a-4c76-9bf4-e7aa94a9f241
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_609d0ef3_f673_413c_a21e_b454ce78643f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_609d0ef3_f673_413c_a21e_b454ce78643f_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : HasPlanarDrawingOn W)
    (hcard : 3 ≤ Fintype.card V)
    (hbelow :
      letI : DecidableRel W.Adj := Classical.decRel W.Adj
      W.edgeFinset.card < 3 * Fintype.card V - 6) :
    ∃ X : SimpleGraph V, W ≤ X ∧ X ≠ W ∧ HasPlanarDrawingOn X := by
  classical
  obtain ⟨X, hWX, hXdraw, hXmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_609d0ef3_f673_413c_a21e_b454ce78643f_a1
      W hW
  have hXbound :=
    WilliamsonShmoys.maximal_planar_edge_bound__p2m_609d0ef3_f673_413c_a21e_b454ce78643f_a1
      X hXdraw hcard hXmax
  have hne : X ≠ W := by
    intro h
    subst X
    letI : DecidableRel W.Adj := Classical.decRel W.Adj
    omega
  exact ⟨X, hWX, hne, hXdraw⟩
