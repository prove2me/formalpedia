-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:10.012864+00:00
-- url     : https://prove2.me/submissions/bd3e8021-e539-41a8-a960-35715d6d6543
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_step__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨K, hKdec, hHK, hKdrawing, hKmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1 H hH
  have hKconnected : K.Connected := by
    by_contra hKdisconnected
    obtain ⟨L, hLdec, hKL, hLdrawing⟩ :=
      WilliamsonShmoys.planar_drawing_bridge_step__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1
        K hKdrawing hcard hKdisconnected
    exact hKmax L hLdec hKL hLdrawing
  exact ⟨K, hKdec, hHK, hKconnected, hKdrawing⟩