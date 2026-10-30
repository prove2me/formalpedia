-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_euler_identity_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:43:20.491494+00:00
-- url     : https://prove2.me/submissions/a6b2e379-3073-4ac4-8325-c380e793df71

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_completion_with_maximal_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hConnected : K.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨H, hKH, hH, hcount⟩ :=
    WilliamsonShmoys.connected_drawing_completion_with_maximal_edge_count K hK hCard
  have hHK : H.edgeSet ⊆ K.edgeSet := hmax H hKH hH
  have hEq : H.edgeSet = K.edgeSet := Set.Subset.antisymm hHK hKH
  simpa [hEq] using hcount.symm