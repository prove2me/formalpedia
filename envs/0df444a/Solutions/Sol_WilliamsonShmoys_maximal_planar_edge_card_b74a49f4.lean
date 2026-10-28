-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_card_b74a49f4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:21:22.642755+00:00
-- url     : https://prove2.me/submissions/fb81c309-9fb7-4db2-aece-ddf7d4a586d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_b74a49f4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_b74a49f4

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.planar_edge_upper_bound_b74a49f4 K hK hCard
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound_b74a49f4
      K hK hCard hmax
  omega