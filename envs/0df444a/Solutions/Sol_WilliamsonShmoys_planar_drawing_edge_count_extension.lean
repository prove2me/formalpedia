-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:23:14.200271+00:00
-- url     : https://prove2.me/submissions/b8f31f8f-e9f9-4bf2-a441-765bf34ea882
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_same_vertices_784d1fda_4529_43fd_94a5_bf399d6fa183
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_784d1fda_4529_43fd_94a5_bf399d6fa183

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 <= Fintype.card V)
    (hE : P.edgeSet.ncard < 3 * Fintype.card V - 6) :
    Exists (fun Q : SimpleGraph V =>
      And (P.edgeSet ⊂ Q.edgeSet)
      (WilliamsonShmoys.HasPlanarDrawingOn Q)) := by
  let hdata := WilliamsonShmoys.planar_drawing_maximal_extension_same_vertices_784d1fda_4529_43fd_94a5_bf399d6fa183 P hP
  let Q := hdata.choose
  have hparts := hdata.choose_spec
  have hPQ := hparts.left
  have hQ := hparts.right.left
  have hmax := hparts.right.right
  have hQcard :
      Q.edgeSet.ncard = 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_784d1fda_4529_43fd_94a5_bf399d6fa183 Q hQ hV hmax
  have hne : P.edgeSet ≠ Q.edgeSet := by
    intro heq
    have hcard : P.edgeSet.ncard = Q.edgeSet.ncard := congrArg Set.ncard heq
    rw [hQcard] at hcard
    omega
  have hstrict : P.edgeSet ⊂ Q.edgeSet :=
    Set.ssubset_iff_subset_ne.mpr ⟨hPQ, hne⟩
  exact ⟨Q, hstrict, hQ⟩