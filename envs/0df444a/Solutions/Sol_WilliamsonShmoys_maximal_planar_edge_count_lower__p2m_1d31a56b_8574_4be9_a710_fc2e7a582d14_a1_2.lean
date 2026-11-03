-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_1d31a56b_8574_4be9_a710_fc2e7a582d14_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:42:14.98197+00:00
-- url     : https://prove2.me/submissions/ea37247d-82fe-423a-909f-69f7245c5040

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1 K hK hcard hmax