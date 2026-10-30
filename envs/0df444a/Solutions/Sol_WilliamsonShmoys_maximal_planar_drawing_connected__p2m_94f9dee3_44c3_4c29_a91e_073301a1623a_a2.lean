-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:55:20.6653+00:00
-- url     : https://prove2.me/submissions/a080d397-cbe5-4a6f-ad67-60fd71114a30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_extension__p2m_4d39bfdd_3b15_4c53_aa35_0f292c6309dd_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
      K.edgeFinset ⊆ L.edgeFinset →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeFinset ⊆ K.edgeFinset) :
    K.Connected := by
  classical
  by_contra hconn
  obtain ⟨L, hLdec, hstrict, hL⟩ :=
    WilliamsonShmoys.planar_drawing_edge_extension__p2m_4d39bfdd_3b15_4c53_aa35_0f292c6309dd_a1
      K hK hcard hconn
  letI : DecidableRel L.Adj := hLdec
  have hback : L.edgeFinset ⊆ K.edgeFinset :=
    hmax L hstrict.1 hL
  exact hstrict.2 hback