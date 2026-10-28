-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:56:31.058426+00:00
-- url     : https://prove2.me/submissions/853cf383-d877-4227-9935-cff3626749ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulation_extension__p2m_c18646d9_4532_475f_9987_0b2cce81491a_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hM, hLM, hCount⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulation_extension__p2m_c18646d9_4532_475f_9987_0b2cce81491a_a1
      L hL hCard
  have hEq : L = M := hMax M hM hLM
  rw [hEq, ← hCount]