-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_card_lower_bound_f3620a14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:30:46.808794+00:00
-- url     : https://prove2.me/submissions/57dc976f-2966-4dae-810e-67db3e3d53d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_dense_supergraph_f3620a14

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R → S ≤ R → R ≤ S) :
    3 * Fintype.card V - 6 ≤ S.edgeSet.ncard := by
  obtain ⟨R, hR, hSR, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_has_dense_supergraph_f3620a14 S hS hCard
  have hRS : R ≤ S := hmax R hR hSR
  have heq : S = R := le_antisymm hSR hRS
  simpa [heq] using hbound