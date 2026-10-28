-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:22:11.293208+00:00
-- url     : https://prove2.me/submissions/6731862f-a6c3-427a-a23a-3891163c64a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_same_vertex_count_20261027

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ H : SimpleGraph V, G.edgeSet ⊂ H.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn H) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hHDraw, hHCount⟩ :=
    WilliamsonShmoys.maximal_planar_extension_same_vertex_count_20261027 G hV hDraw
  have hEq : G.edgeSet = H.edgeSet := by
    apply Set.Subset.antisymm hGH
    intro e he
    by_contra hNotG
    have hne : G.edgeSet ≠ H.edgeSet := by
      intro heq
      have heG : e ∈ G.edgeSet := by simpa [heq] using he
      exact hNotG heG
    have hStrict : G.edgeSet ⊂ H.edgeSet :=
      Set.ssubset_iff_subset_ne.mpr ⟨hGH, hne⟩
    exact hMax H hStrict hHDraw
  have hCard : G.edgeSet.ncard = H.edgeSet.ncard := congrArg Set.ncard hEq
  exact hCard.trans hHCount