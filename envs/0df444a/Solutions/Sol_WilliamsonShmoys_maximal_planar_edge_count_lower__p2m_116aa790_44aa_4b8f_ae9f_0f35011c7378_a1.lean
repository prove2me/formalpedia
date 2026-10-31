-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:06:09.487611+00:00
-- url     : https://prove2.me/submissions/a3d9634a-6473-4ba5-9211-f4595354f826

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_below_planar_bound_has_drawable_strict_supergraph__p2m_b704201f_fc6b_4e4c_b576_9e83647d88b7_a1
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  by_contra hBound
  have hlt : K.edgeSet.ncard < 3 * Fintype.card V - 6 :=
    Nat.lt_of_not_ge hBound
  obtain ⟨L, hKL, hLDraw⟩ :=
    WilliamsonShmoys.drawable_graph_below_planar_bound_has_drawable_strict_supergraph__p2m_b704201f_fc6b_4e4c_b576_9e83647d88b7_a1
      K hK hCard hlt
  have hLK : L ≤ K := hMax L (le_of_lt hKL) hLDraw
  exact (not_le_of_gt hKL) hLK