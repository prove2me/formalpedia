-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:10:18.775749+00:00
-- url     : https://prove2.me/submissions/b34a6452-9cf0-416b-963d-0301fddc0724
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_ctx816e1e7a
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_mono_ctx816e1e7a
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_ctx816e1e7a
import Mathlib.Tactic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hsmall : Z.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ W : SimpleGraph V,
      Z < W ∧ WilliamsonShmoys.HasPlanarDrawingOn W := by
  obtain ⟨W, hZW, hWdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_ctx816e1e7a Z hZ
  have hmono := WilliamsonShmoys.planar_edge_count_mono_ctx816e1e7a Z W hZW
  have hbound := WilliamsonShmoys.maximal_planar_edge_lower_bound_ctx816e1e7a W hV hWdraw hmax
  have hcount : Z.edgeSet.ncard < W.edgeSet.ncard := by omega
  have hneq : Z ≠ W := by
    intro heq
    subst W
    omega
  exact ⟨W, lt_of_le_of_ne hZW hneq, hWdraw⟩