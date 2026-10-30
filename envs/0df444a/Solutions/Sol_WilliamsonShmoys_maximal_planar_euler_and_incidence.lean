-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_and_incidence
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:12:42.334784+00:00
-- url     : https://prove2.me/submissions/b32c7201-a10a-46c9-9d31-77684b5ef858

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_card

set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hMax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = J.edgeSet.ncard + 2 ∧
      3 * f = 2 * J.edgeSet.ncard := by
  have hEdges := WilliamsonShmoys.maximal_planar_edge_card J hJ hMax hCard
  refine ⟨2 * Fintype.card V - 4, ?_⟩
  constructor <;> omega