-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:15:09.896362+00:00
-- url     : https://prove2.me/submissions/bfe3d330-09e3-4066-b95e-f830d1a3d460

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      (∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => L ≤ G ∧ HasPlanarDrawingOn G
  have hL : L ∈ candidates := by
    simp [candidates, hDraw]
  obtain ⟨T, hTmem, hTmax⟩ :=
    Finset.exists_max_image candidates (fun G => Fintype.card G.edgeSet) ⟨L, hL⟩
  have hLT : L ≤ T := (Finset.mem_filter.mp hTmem).2.1
  have hTdraw : HasPlanarDrawingOn T := (Finset.mem_filter.mp hTmem).2.2
  refine ⟨T, hLT, hTdraw, ?_⟩
  intro U hTU hUdraw
  have hLU : L ≤ U := le_trans hLT hTU
  have hUmem : U ∈ candidates := by
    simp [candidates, hLU, hUdraw]
  have hCardLE : Fintype.card U.edgeSet ≤ Fintype.card T.edgeSet := hTmax U hUmem
  have hEdges : T.edgeSet ⊆ U.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hTU
  have hEdgesEq : T.edgeSet = U.edgeSet :=
    Set.eq_of_subset_of_card_le hEdges hCardLE
  have hTUeq : T = U := SimpleGraph.edgeSet_inj.mp hEdgesEq
  simpa [hTUeq]