-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:29:50.766372+00:00
-- url     : https://prove2.me/submissions/c8b2e2da-e7b4-4793-9d28-691175713132
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulating_supergraph__p2m_2fdbe618_fdb5_40d5_afa9_43a53e53fa32_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulating_supergraph__p2m_2fdbe618_fdb5_40d5_afa9_43a53e53fa32_a1 K hK hV
  have hLK : L = K := hmax L hKL hL
  subst L
  exact hcount.le