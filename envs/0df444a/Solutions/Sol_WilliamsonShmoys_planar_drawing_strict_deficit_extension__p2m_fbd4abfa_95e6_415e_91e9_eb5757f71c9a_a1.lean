-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_strict_deficit_extension__p2m_fbd4abfa_95e6_415e_91e9_eb5757f71c9a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:22:00.727819+00:00
-- url     : https://prove2.me/submissions/02dee4c6-b440-4674-8bcf-0bb5d019602b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hConn : ∀ u v, Relation.ReflTransGen K.Adj u v)
    (hV : 3 ≤ Fintype.card V)
    (hDeficit : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ L ≠ K ∧ HasPlanarDrawingOn L := by
  obtain ⟨L, hKL, hLDraw, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1
      K hDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1
      L hLDraw hMax hV
  have hNe : L ≠ K := by
    intro h
    subst L
    omega
  exact ⟨L, hKL, hNe, hLDraw⟩
