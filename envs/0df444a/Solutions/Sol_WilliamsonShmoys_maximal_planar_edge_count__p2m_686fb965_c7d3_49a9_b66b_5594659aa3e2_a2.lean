-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_686fb965_c7d3_49a9_b66b_5594659aa3e2_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:49:16.577837+00:00
-- url     : https://prove2.me/submissions/277c9b68-ac25-430e-8add-6335bb7d6367
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_4d9bb183_475b_4a59_8b75_1a8cda8dae1d_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_4d9bb183_475b_4a59_8b75_1a8cda8dae1d_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      L <= K → HasPlanarDrawingOn K → K = L) :
    letI : DecidableRel L.Adj := dL
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hlow := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_4d9bb183_475b_4a59_8b75_1a8cda8dae1d_a2
    L dL hL hcard hmax
  have hupp := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_4d9bb183_475b_4a59_8b75_1a8cda8dae1d_a2
    L dL hL hcard
  omega
