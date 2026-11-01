-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximum_planar_supergraph__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:06:47.904827+00:00
-- url     : https://prove2.me/submissions/af83ccae-7d76-468d-97f6-8af54e711f5c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_maximal_edge_count__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_le__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeFinset ⊆ K.edgeFinset ∧
      ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeFinset.card ≥ L.edgeFinset.card := by
  let M : ℕ := if Fintype.card V < 3 then (Fintype.card V).choose 2
    else 3 * Fintype.card V - 6
  obtain ⟨K, dK, hK, hHK, hKM⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_maximal_edge_count__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
      H dH hH
  refine ⟨K, dK, hK, SimpleGraph.edgeFinset_subset_edgeFinset.mpr hHK, ?_⟩
  intro L dL hL
  have hLM := WilliamsonShmoys.planar_edge_count_le__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
    L dL hL
  calc
    K.edgeFinset.card = M := by simpa [M] using hKM
    _ ≥ L.edgeFinset.card := by simpa [M] using hLM