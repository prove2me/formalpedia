-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:33.974424+00:00
-- url     : https://prove2.me/submissions/19a762ea-f35b-4b51-a29e-f0c18d7d7d81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound__p2m_c7faf2fe_bfe2_4bd3_9a36_edfb3235a50d_a1
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : LE.le 3 (Fintype.card V))
    (hmax : (L : SimpleGraph V) -> LE.le K L -> HasPlanarDrawingOn L -> LE.le L K) :
    LE.le (3 * Fintype.card V) (K.edgeSet.ncard + 6) := by
  obtain ⟨L, hKL, hL, hbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_bound__p2m_c7faf2fe_bfe2_4bd3_9a36_edfb3235a50d_a1
      K hK hV
  have hLK : LE.le L K := hmax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  simpa [hEq] using hbound