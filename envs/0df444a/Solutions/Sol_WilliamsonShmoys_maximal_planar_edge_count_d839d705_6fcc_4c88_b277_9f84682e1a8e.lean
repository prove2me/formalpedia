-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_d839d705_6fcc_4c88_b277_9f84682e1a8e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:38:40.006105+00:00
-- url     : https://prove2.me/submissions/aa665348-41c2-477b-b1ac-ad9574783a41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_triangulation_completion_aa4e0804

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  let completion :=
    WilliamsonShmoys.planar_edge_count_triangulation_completion_aa4e0804
      K hV hK
  let H := Classical.choose completion
  have hprops := Classical.choose_spec completion
  have hKH : K <= H := hprops.1
  have hH : WilliamsonShmoys.HasPlanarDrawingOn H := hprops.2.1
  have hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V := hprops.2.2
  have hHK : H = K := hmax H hKH hH
  have hedge : H.edgeSet.ncard = K.edgeSet.ncard :=
    congrArg (fun L : SimpleGraph V => L.edgeSet.ncard) hHK
  omega