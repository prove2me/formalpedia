-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_supergraph_large_9dbc1b44_5e81_4cbc_9338_84418c6013a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:18:30.813+00:00
-- url     : https://prove2.me/submissions/e6fc9836-7955-4ad1-a10a-c9f5ce5db2c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_one_edge_extension_nonempty
import Theorems.Thm_WilliamsonShmoys_planar_extension_step_closes

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected := by
  obtain ⟨H, hGH, hH, hConn⟩ :=
    WilliamsonShmoys.planar_extension_step_closes G hG (by
      intro K hGK hK hKDisconnected
      exact WilliamsonShmoys.planar_drawing_one_edge_extension_nonempty
        K hK hCard hKDisconnected)
  refine ⟨H, ?_, hH, hConn⟩
  intro u v hAdj
  exact hGH hAdj