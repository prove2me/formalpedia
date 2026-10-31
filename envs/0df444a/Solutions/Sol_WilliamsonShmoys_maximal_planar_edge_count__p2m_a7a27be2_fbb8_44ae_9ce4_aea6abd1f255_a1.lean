-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_a7a27be2_fbb8_44ae_9ce4_aea6abd1f255_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:30:05.112445+00:00
-- url     : https://prove2.me/submissions/8af07458-fcc1-4dec-9a53-57bc0409daaa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_42afe04b_4ecc_4d48_9c38_07e79025e31e_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hcomp :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_42afe04b_4ecc_4d48_9c38_07e79025e31e_a2
      K hK hV
  let H := Classical.choose hcomp
  have hprops : K <= H /\ WilliamsonShmoys.HasPlanarDrawingOn H /\
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := Classical.choose_spec hcomp
  have hKH : K <= H := hprops.1
  have hHprops : WilliamsonShmoys.HasPlanarDrawingOn H /\
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := hprops.2
  have hH : WilliamsonShmoys.HasPlanarDrawingOn H := hHprops.1
  have hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V := hHprops.2
  have hHK : H <= K := hmax H hKH hH
  have hEq : H = K := by
    ext u v
    constructor <;> intro huv <;> first | exact hHK huv | exact hKH huv
  simpa [hEq] using hcount