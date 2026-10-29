-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:05:09.980598+00:00
-- url     : https://prove2.me/submissions/4f623221-3f7b-420c-b934-e331c7798ec9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * (Fintype.card V : Int) - 6 <= (M.edgeSet.ncard : Int) := by
  obtain ⟨N, hMN, hN, hNbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_lower_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421 M hV hM
  have hNM : N ≤ M := hmax N hMN hN
  have hEq : M = N := le_antisymm hMN hNM
  simpa [hEq] using hNbound