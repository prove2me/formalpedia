-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_graph_for_f2fc27dd
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:58:41.934864+00:00
-- url     : https://prove2.me/submissions/428cb875-2c71-4edc-9eec-bede01c9e78a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count_candidate

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_edge_count_candidate K hV hK
  have hLK : L = K := hmax L hKL hL
  rw [hLK] at hcount
  exact hcount