-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_f3620a14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T14:06:29.960488+00:00
-- url     : https://prove2.me/submissions/fba76a37-f8a1-488c-94f8-37439f748fd8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_f3620a14

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S → T ≤ S → S ≤ T)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  obtain ⟨S, hS, hTS, hEdges⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension_f3620a14 T hT hCard
  have hST : S ≤ T := hmax S hS hTS
  have hEq : T = S := le_antisymm hTS hST
  rw [← hEq] at hEdges
  omega