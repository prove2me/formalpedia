-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:03:17.982953+00:00
-- url     : https://prove2.me/submissions/79c05f4b-f6b0-49ef-ac25-32bc66cb09c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_exact_edge_count_for_f2fc27dd

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_completion_exact_edge_count_for_f2fc27dd H hV hH
  have hKH : K = H := hmax K hHK hK
  rw [← hKH]
  exact hcount