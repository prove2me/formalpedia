-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:15:08.682423+00:00
-- url     : https://prove2.me/submissions/f4327d74-8b9e-44c3-86d2-bedcfa5dd24e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_3afafa65_8e09_4130_830e_45057f389001_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  letI : DecidableRel U.Adj := dU
  obtain ⟨W, dW, hsub, hW, hcard_eq, hcard_le⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_3afafa65_8e09_4130_830e_45057f389001_a1
      U dU hU hcard
  letI : DecidableRel W.Adj := dW
  omega
