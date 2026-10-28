-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition_f3620a14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:48:27.69932+00:00
-- url     : https://prove2.me/submissions/a691e175-bdca-45fb-a848-f14a76125fde
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_f3620a14
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_f3620a14

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S → T ≤ S → S ≤ T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = T.edgeSet.ncard + 2 ∧
      3 * f = 2 * T.edgeSet.ncard := by
  have hUpper := WilliamsonShmoys.planar_edge_bound_f3620a14 T hT hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound_f3620a14 T hT hmax hCard
  have hEdge : T.edgeSet.ncard + 6 = 3 * Fintype.card V := by omega
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega