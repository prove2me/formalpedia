-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_six_offset_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:23:42.643815+00:00
-- url     : https://prove2.me/submissions/9d15a9e0-23a0-4166-9c1b-6d79c19f6ddd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_certificate
import Theorems.Thm_WilliamsonShmoys_euler_certificate_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, HasPlanarDrawingOn X →
      (∀ u v, W.Adj u v → X.Adj u v) →
      ∀ u v, X.Adj u v → W.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by
  have hEq := WilliamsonShmoys.euler_certificate_exact_edge_count W
    (WilliamsonShmoys.maximal_planar_drawing_has_euler_certificate
      W hW hmax hCard)
  omega