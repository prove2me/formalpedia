-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_7b71df04_d9fa_431d_9970_a3959e705ba4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:38:38.038948+00:00
-- url     : https://prove2.me/submissions/106ebc77-1c03-4932-8216-092a157cbffd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_9f0d58b7_b6f9_47f0_b3be_8c258362d568_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKplanar, hKedges⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_9f0d58b7_b6f9_47f0_b3be_8c258362d568_a2
      H hcard hplanar
  have hKH : K = H := hmax K hHK hKplanar
  subst K
  omega