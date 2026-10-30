-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_c3d7847a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:04:54.198752+00:00
-- url     : https://prove2.me/submissions/d68094a6-243e-45be-9fcd-e17f9d28c057

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_with_triangulated_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, J.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K → K.edgeSet = J.edgeSet) :
    J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hSub, hKDraw, hCount⟩ :=
    WilliamsonShmoys.drawable_supergraph_with_triangulated_edge_count
      J hDraw hCard
  have hEdges : K.edgeSet = J.edgeSet := hMax K hSub hKDraw
  have hCardEdges : K.edgeSet.ncard = J.edgeSet.ncard :=
    congrArg (fun s : Set (Sym2 V) => s.ncard) hEdges
  omega