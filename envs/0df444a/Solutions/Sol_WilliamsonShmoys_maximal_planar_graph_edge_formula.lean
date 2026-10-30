-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:24:05.011335+00:00
-- url     : https://prove2.me/submissions/15039723-54e6-41be-b432-0de7972a96aa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_planar_graph_add_edge_below_max

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hMax : ∀ S : SimpleGraph V, R ≤ S →
      WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hLower : 3 * Fintype.card V - 6 ≤ R.edgeSet.ncard := by
    by_contra h
    have hSmall : R.edgeSet.ncard < 3 * Fintype.card V - 6 := Nat.lt_of_not_ge h
    obtain ⟨S, hRS, hSdraw⟩ :=
      WilliamsonShmoys.planar_graph_add_edge_below_max R hV hRdraw hSmall
    have hEq : S = R := hMax S (le_of_lt hRS) hSdraw
    subst S
    exact (lt_irrefl _ hRS)
  have hUpper := WilliamsonShmoys.planar_graph_edge_upper_bound R hV hRdraw
  omega