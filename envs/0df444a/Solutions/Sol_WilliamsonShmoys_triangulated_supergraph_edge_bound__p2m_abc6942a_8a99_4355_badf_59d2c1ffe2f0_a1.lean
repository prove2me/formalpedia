-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_abc6942a_8a99_4355_badf_59d2c1ffe2f0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:18:53.384884+00:00
-- url     : https://prove2.me/submissions/c9aee3b8-06be-4750-a2bb-8f94beaff35e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    exists K : SimpleGraph V,
      M <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
        3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  let hExist :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1
      M hM
  let K := Classical.choose hExist
  have hSpec := Classical.choose_spec hExist
  cases hSpec with
  | intro hMK hSpec2 =>
    cases hSpec2 with
    | intro hKdraw hMax =>
      refine Exists.intro K ?_
      exact And.intro hMK (And.intro hKdraw
        (WilliamsonShmoys.maximal_planar_edge_bound__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1
          K hKdraw hV hMax))