-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:42:30.810452+00:00
-- url     : https://prove2.me/submissions/143a0f0d-495b-457b-b0ad-39af1fb91048
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_a8911ec3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  obtain ⟨K, hNK, hK, hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension_a8911ec3 N hV hN
  have hKN : K = N := hmax K hNK hK
  rw [hKN] at hcount
  exact hcount