-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_1cedfa43_e759_4304_8f59_175ee0ad0ade_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:11:48.008968+00:00
-- url     : https://prove2.me/submissions/bc76edd4-d51c-4876-9587-42a62a2e8997
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_spanning_triangulation_edge_count__p2m_8ce49ca9_f099_4adf_900b_33def51c5366_a2

set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨M, hLM, hMD, hCount⟩ :=
    WilliamsonShmoys.planar_spanning_triangulation_edge_count__p2m_8ce49ca9_f099_4adf_900b_33def51c5366_a2
      L hDraw hV
  have hEq : M = L := hMax M hLM hMD
  simpa [hEq] using (le_of_eq hCount.symm)