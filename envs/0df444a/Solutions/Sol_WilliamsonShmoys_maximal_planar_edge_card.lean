-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:27:39.723552+00:00
-- url     : https://prove2.me/submissions/1f8908b2-54ae-4b61-900b-31c9e24ce6b2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_card

set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hMax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J)
    (hCard : 3 ≤ Fintype.card V) : J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hJK, hKplanar, hKcard⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_edge_card J hJ hCard
  have hEq : K = J := hMax K hJK hKplanar
  rw [hEq] at hKcard
  exact hKcard