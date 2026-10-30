-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangulation_counts__p2m_08343436_3ed5_44fc_aeba_2ee2e4a22301_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:42:40.488871+00:00
-- url     : https://prove2.me/submissions/aa2b1f33-ccc9-4b06-bfc4-e93080d28914

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_has_triangulation_edge_count__p2m_80d3c120_40ab_4263_83fa_69737aacfbab_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    exists f : Nat, Fintype.card V + f = K.edgeSet.ncard + 2 /\
      3 * f = 2 * K.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hEdges⟩ :=
    WilliamsonShmoys.planar_extension_has_triangulation_edge_count__p2m_80d3c120_40ab_4263_83fa_69737aacfbab_a1
      K hK hV
  have hLK : L = K := hMax L hKL hL
  subst L
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega