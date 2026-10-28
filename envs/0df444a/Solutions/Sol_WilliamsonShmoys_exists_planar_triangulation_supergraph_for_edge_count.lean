-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph_for_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:47:17.245121+00:00
-- url     : https://prove2.me/submissions/a11ff04d-2304-43ce-8fac-c1f11588f063
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_drawing_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Q.Connected) :
    ∃ M : SimpleGraph V,
      Q ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  obtain ⟨M, hQM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_planar_drawing_maximal_supergraph Q hQ hconn
  have hcount :=
    WilliamsonShmoys.planar_maximal_supergraph_edge_count M hM hV hmax
  exact ⟨M, hQM, hM, hcount⟩