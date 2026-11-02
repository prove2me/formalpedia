-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:21:35.626205+00:00
-- url     : https://prove2.me/submissions/f60d5c2c-952c-4a24-aa70-2bf9c9349e8f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_extension__p2m_0a0c7b94_7c6b_416a_9a27_7e1438879d42_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hR : HasPlanarDrawingOn R)
    (hMax : ∀ H : SimpleGraph V, R ≤ H → HasPlanarDrawingOn H → H = R) :
    (letI : DecidableRel R.Adj := Classical.decRel R.Adj
     3 * Fintype.card V = R.edgeFinset.card + 6) := by
  obtain ⟨T, hRT, hTdrawing, hTcount⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_0a0c7b94_7c6b_416a_9a27_7e1438879d42_a1
      R hV hR
  have hTR : T = R := hMax T hRT hTdrawing
  subst T
  simpa using hTcount