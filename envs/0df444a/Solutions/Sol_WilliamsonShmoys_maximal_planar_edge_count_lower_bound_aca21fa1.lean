-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_aca21fa1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:50:26.624128+00:00
-- url     : https://prove2.me/submissions/ac6a42f1-8fef-4485-a06a-11a1f4162eaf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_count_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : HasPlanarDrawingOn Z)
    (hCard : 3 <= Fintype.card V)
    (hmax : (W : SimpleGraph V) -> HasPlanarDrawingOn W ->
      ((u v : V) -> Z.Adj u v -> W.Adj u v) ->
      (u v : V) -> W.Adj u v -> Z.Adj u v) :
    3 * (Fintype.card V : Int) - 6 <= (Z.edgeSet.ncard : Int) := by
  obtain ⟨W, hW, hZW, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_completion_edge_count_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b
      Z hZ hCard
  have hWZ : (u v : V) -> W.Adj u v -> Z.Adj u v := hmax W hW hZW
  have hEq : Z = W := by
    ext u v
    exact ⟨hZW u v, hWZ u v⟩
  rw [← hEq] at hEdges
  omega