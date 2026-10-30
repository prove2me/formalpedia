-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_742e15ee_6999_43aa_960c_9e8cbc35dbfd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:15:26.502418+00:00
-- url     : https://prove2.me/submissions/8daba62f-11ba-45de-aa55-9511713a7d79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_extension__p2m_9379b763_2dc6_43e2_b02a_b18a7334854d_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  by_contra h
  have hdef : M.edgeSet.ncard + 6 < 3 * Fintype.card V := Nat.lt_of_not_ge h
  obtain ⟨K, hMK, hK⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_extension__p2m_9379b763_2dc6_43e2_b02a_b18a7334854d_a1
      M hM hV hdef
  have hKM : K ≤ M := hMax K (le_of_lt hMK) hK
  exact (not_le_of_gt hMK) hKM