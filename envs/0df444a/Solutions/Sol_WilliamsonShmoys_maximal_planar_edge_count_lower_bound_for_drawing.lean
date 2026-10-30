-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_for_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:25:03.331402+00:00
-- url     : https://prove2.me/submissions/d573f0f0-5a5e-4a37-9f9a-0330ea7d9f9a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_on

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hKmax : IsMaximalPlanarOn K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨H, hKH, hHplanar, hHcount⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_supergraph_on K hKmax.1 hV
  rcases hKmax with ⟨_, hmax⟩
  have hHK : H = K := hmax H hKH hHplanar
  rw [hHK] at hHcount
  exact le_of_eq hHcount.symm