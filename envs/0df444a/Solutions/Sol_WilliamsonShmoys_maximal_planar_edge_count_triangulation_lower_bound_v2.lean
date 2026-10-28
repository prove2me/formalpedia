-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_triangulation_lower_bound_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:59:16.279862+00:00
-- url     : https://prove2.me/submissions/de4534c9-04cb-4808-bad5-2a199149af91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_edge_count K hV hK
  have hLK : L ≤ K := hmax L hKL hL
  have hEq : K = L := le_antisymm hKL hLK
  rw [hEq]
  exact le_of_eq hcount