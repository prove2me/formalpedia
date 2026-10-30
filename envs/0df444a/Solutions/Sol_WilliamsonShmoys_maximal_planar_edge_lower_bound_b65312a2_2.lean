-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound_b65312a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:27:11.121375+00:00
-- url     : https://prove2.me/submissions/e6a0713e-0808-4217-b469-497e2afca856

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_b65312a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNdraw, hNcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulated_extension_b65312a2 M hV hMdraw
  have hNM : N = M := hMmax N hMN hNdraw
  rw [hNM] at hNcard
  exact le_of_eq hNcard