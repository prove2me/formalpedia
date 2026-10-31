-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:18:08.257682+00:00
-- url     : https://prove2.me/submissions/8574d8e3-a277-40b0-b105-d5d030b8e424

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_75785758_9f27_4736_ab49_77b09febfcc3_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨H, hKH, hH, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation__p2m_75785758_9f27_4736_ab49_77b09febfcc3_a1 K hK hV
  have hHK : H <= K := hmax H hKH hH
  have hEq : H = K := le_antisymm hHK hKH
  rw [hEq] at hcount
  exact hcount.le