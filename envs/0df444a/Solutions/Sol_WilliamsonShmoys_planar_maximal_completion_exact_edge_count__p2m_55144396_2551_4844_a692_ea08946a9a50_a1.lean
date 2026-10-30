-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_completion_exact_edge_count__p2m_55144396_2551_4844_a692_ea08946a9a50_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:55:33.599194+00:00
-- url     : https://prove2.me/submissions/2dbdcefc-546e-44f1-af04-7d6b273bac10
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_exists__p2m_e74de359_8181_429e_92f3_9fe027354fb5_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_e74de359_8181_429e_92f3_9fe027354fb5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    exists K : SimpleGraph V, N <= K /\ HasPlanarDrawingOn K /\
      (letI : DecidableRel K.Adj := Classical.decRel _;
       K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension_exists__p2m_e74de359_8181_429e_92f3_9fe027354fb5_a1 N hN
  refine ⟨K, hNK, hK, ?_⟩
  letI : DecidableRel K.Adj := Classical.decRel _
  exact WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_e74de359_8181_429e_92f3_9fe027354fb5_a1 K hK hcard hmax