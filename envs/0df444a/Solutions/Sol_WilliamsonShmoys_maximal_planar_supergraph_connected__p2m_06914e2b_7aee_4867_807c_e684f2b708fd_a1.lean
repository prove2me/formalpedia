-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:46:14.67974+00:00
-- url     : https://prove2.me/submissions/8626dca7-fe47-4375-8ed4-1f41fa1d228a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_strict_supergraph_of_not_connected__p2m_bc735298_99fb_476e_aa8d_1e3af7f2e774_a1
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKplanar : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ K.edgeSet.ncard)
    (hV : 3 ≤ Fintype.card V) : K.Connected := by
  by_contra hconn
  obtain ⟨L, hKL, hLplanar, hcard⟩ :=
    WilliamsonShmoys.exists_planar_strict_supergraph_of_not_connected__p2m_bc735298_99fb_476e_aa8d_1e3af7f2e774_a1 K hKplanar hconn
  have hmaxL := hmax L hKL hLplanar
  omega