-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_79011c86fe2a4d17
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:52:31.605948+00:00
-- url     : https://prove2.me/submissions/656ba9ec-6bcd-43f0-a48c-649c26dab740

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_lower_bound

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P ≤ N) :
    3 * Fintype.card V - 6 <= N.edgeSet.ncard := by
  obtain ⟨P, hNP, hP, hbound⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound N hV hN
  have hPN : P ≤ N := hmax P hNP hP
  have hEq : P = N := le_antisymm hPN hNP
  simpa [hEq] using hbound