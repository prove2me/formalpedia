-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_from_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:28:49.42998+00:00
-- url     : https://prove2.me/submissions/1b9d4e3e-797d-439f-a8ab-616de5170172

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨N, hMN, hNdraw, hNbound⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_edge_bound M hV hMdraw
  have hNM : N ≤ M := hMmax N hMN hNdraw
  have hEq : N = M := le_antisymm hNM hMN
  simpa [hEq] using hNbound
