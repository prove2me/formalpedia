-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:51:05.328436+00:00
-- url     : https://prove2.me/submissions/461cd22d-ca70-4a9f-8a60-1432dcb6b53a

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_upper_bound K hK hCard
