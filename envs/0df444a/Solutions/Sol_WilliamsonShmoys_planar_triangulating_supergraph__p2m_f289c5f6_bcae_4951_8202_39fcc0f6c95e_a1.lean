-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulating_supergraph__p2m_f289c5f6_bcae_4951_8202_39fcc0f6c95e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:56:46.881114+00:00
-- url     : https://prove2.me/submissions/82fcab06-0d95-4e3e-a070-7e132d1e6198

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4

set_option autoImplicit false

open scoped BigOperators

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    Exists fun N : SimpleGraph V => And (LE.le M N)
      (And (WilliamsonShmoys.HasPlanarDrawingOn N)
        (And (Nat.le M.edgeSet.ncard N.edgeSet.ncard)
          (N.edgeSet.ncard = 3 * Fintype.card V - 6))) := by
  classical
  let N : SimpleGraph V := Classical.choose
    (WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4
      M hplanar)
  have hprops := Classical.choose_spec
    (WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4
      M hplanar)
  have hMN : LE.le M N := hprops.1
  have hNplanar : WilliamsonShmoys.HasPlanarDrawingOn N := hprops.2.1
  have hmono : Nat.le M.edgeSet.ncard N.edgeSet.ncard := hprops.2.2.1
  have hmax := hprops.2.2.2
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4
      N hNplanar hcard hmax
  exact Exists.intro N (And.intro hMN (And.intro hNplanar (And.intro hmono hcount)))