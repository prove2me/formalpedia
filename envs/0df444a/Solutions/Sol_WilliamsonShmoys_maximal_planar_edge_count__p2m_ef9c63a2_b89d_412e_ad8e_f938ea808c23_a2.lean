-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:58:44.117561+00:00
-- url     : https://prove2.me/submissions/7f59a335-d48a-45d6-b505-610c0fcac9db

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_4c578d9c_5ad8_4ad5_bf9f_68265b93ec4b_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_4c578d9c_5ad8_4ad5_bf9f_68265b93ec4b_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_4c578d9c_5ad8_4ad5_bf9f_68265b93ec4b_a2
      K hK hV
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_4c578d9c_5ad8_4ad5_bf9f_68265b93ec4b_a2
      K hK hV hmax
  omega
