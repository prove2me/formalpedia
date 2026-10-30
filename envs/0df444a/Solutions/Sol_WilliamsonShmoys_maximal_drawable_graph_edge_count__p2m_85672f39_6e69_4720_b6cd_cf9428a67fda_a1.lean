-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:28:21.330308+00:00
-- url     : https://prove2.me/submissions/c012bd21-3b59-4f7e-ae25-cced33449c8d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_exact_edge_count__p2m_70a6424f_4889_4ef2_870f_ee6e7e607f96_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_exact_edge_count__p2m_70a6424f_4889_4ef2_870f_ee6e7e607f96_a1
      K hK hV
  have hLK : L = K := hmax L hKL hL
  rw [← hLK]
  exact hCount