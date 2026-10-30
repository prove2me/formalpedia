-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_d16397ab_f97b_4b48_8e65_cb91b43850d6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:29:32.220834+00:00
-- url     : https://prove2.me/submissions/ae43e20a-37f8-49a6-ae10-952297619ef2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_c8d2e80c_d8a1_4ce7_8838_7e9b10da8c57_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ H' : SimpleGraph V, H ≤ H' → HasPlanarDrawingOn H' → H' = H) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hcard⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_c8d2e80c_d8a1_4ce7_8838_7e9b10da8c57_a1
      H hH hV
  have hKH : K = H := hmax K hHK hK
  have hcardH : H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    simpa [hKH] using hcard
  omega