-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_of_disconnected_graph__p2m_8a39e0cf_ef07_4e8d_9689_6d4757ac8893_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:57.294692+00:00
-- url     : https://prove2.me/submissions/cb4c9f18-b0a0-44b0-a32f-d792575ca0fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_add_bridge_between_components__p2m_820a0dbc_c2b9_49d9_bf22_c9c2683d46a8_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) (hdis : ¬ K.Connected) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ¬ L ≤ K := by
  obtain ⟨a, b, hab, hnotAdj, L, hKL, hL, hLab, hnew⟩ :=
    WilliamsonShmoys.planar_add_bridge_between_components__p2m_820a0dbc_c2b9_49d9_bf22_c9c2683d46a8_a2
      K hcard hK hdis
  refine ⟨L, hKL, hL, ?_⟩
  intro hLK
  exact hnotAdj (hLK hLab)