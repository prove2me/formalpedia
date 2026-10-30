-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_drawing_is_dense
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:24:07.889392+00:00
-- url     : https://prove2.me/submissions/9338856c-07a2-4541-8934-f142a85ce433

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_density

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨L, hsub, hL, hbound⟩ :=
    WilliamsonShmoys.planar_extension_density K hK hV
  have heq : L.edgeSet = K.edgeSet := hmax L hsub hL
  rw [← heq]
  exact hbound