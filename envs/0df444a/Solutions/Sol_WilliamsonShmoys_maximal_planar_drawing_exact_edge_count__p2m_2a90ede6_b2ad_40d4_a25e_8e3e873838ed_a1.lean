-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:12:55.456581+00:00
-- url     : https://prove2.me/submissions/cbf6a80c-56ed-4332-803c-b85d03e090d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_deficit_extension__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hConn : ∀ u v, Relation.ReflTransGen K.Adj u v)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1
      K hDraw hV
  by_contra hEq
  have hDeficit : K.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨L, hKL, hNe, hLDraw⟩ :=
    WilliamsonShmoys.planar_drawing_strict_deficit_extension__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1
      K hDraw hConn hV hDeficit
  have hLK : L = K := hMax L hKL hLDraw
  exact hNe hLK