-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:23.733993+00:00
-- url     : https://prove2.me/submissions/ee80fb23-e270-4ac4-b129-fec02f2a1035
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulating_supergraph__p2m_d1b6a74a_dd8a_4218_af86_64a379555708_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.exists_triangulating_supergraph__p2m_d1b6a74a_dd8a_4218_af86_64a379555708_a1
      H hH hV
  have hKH : K ≤ H := hMax K hHK hK
  have hEq : K = H := le_antisymm hKH hHK
  rw [← hEq]
  exact hcount