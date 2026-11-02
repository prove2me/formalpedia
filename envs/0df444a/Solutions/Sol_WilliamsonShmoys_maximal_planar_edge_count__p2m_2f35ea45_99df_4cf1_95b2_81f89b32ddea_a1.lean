-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2f35ea45_99df_4cf1_95b2_81f89b32ddea_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:46:38.079785+00:00
-- url     : https://prove2.me/submissions/81bb212c-e9d1-40c5-8297-0fc8a3862d3f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_34ce151f_05d3_497c_a88f_b630e2f0d090_a1__p2m_34ce151f_05d3_497c_a88f_b630e2f0d090_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L = K)
    (hn : 3 <= Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel _
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_34ce151f_05d3_497c_a88f_b630e2f0d090_a1__p2m_34ce151f_05d3_497c_a88f_b630e2f0d090_a2
      K hK hn
  have hLK : L = K := hmax L hKL hL
  rw [← hLK]
  exact hcount