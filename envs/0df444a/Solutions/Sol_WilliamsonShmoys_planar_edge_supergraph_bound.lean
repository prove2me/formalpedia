-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_supergraph_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:12:42.960112+00:00
-- url     : https://prove2.me/submissions/9e641a9e-a951-42e7-9dc5-f5c1e0f8e850
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension_1a1e4639_984e_4d53_99b4_0a5c82fb99e6
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_1a1e4639_984e_4d53_99b4_0a5c82fb99e6

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hJK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension_1a1e4639_984e_4d53_99b4_0a5c82fb99e6
      J hConn hV hJ
  exact ⟨K, hJK,
    WilliamsonShmoys.maximal_planar_edge_count_1a1e4639_984e_4d53_99b4_0a5c82fb99e6
      K hV hK hMax⟩