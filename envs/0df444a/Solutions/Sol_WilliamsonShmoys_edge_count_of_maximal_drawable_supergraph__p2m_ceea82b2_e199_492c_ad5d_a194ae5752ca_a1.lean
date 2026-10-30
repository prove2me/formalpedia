-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:49:37.212622+00:00
-- url     : https://prove2.me/submissions/31cf02c9-b651-4271-8ace-e71ff18bc14e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_42e17741_b5fb_4586_95ad_fdcb2ee9a443_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = W) :
    W.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨X, hWX, hX, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_42e17741_b5fb_4586_95ad_fdcb2ee9a443_a1
      W hW hV
  have hEq : X = W := hmax X hWX hX
  simpa [hEq] using hcount