-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_euler_count_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:26:14.931781+00:00
-- url     : https://prove2.me/submissions/7c2da58c-8ec4-4ea2-b080-48d3231a5958
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall K : SimpleGraph V, M <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = M) :
    exists f : Nat,
      (Fintype.card V : Int) - (M.edgeSet.ncard : Int) + (f : Int) = 2 /\
      (3 : Int) * (f : Int) = 2 * (M.edgeSet.ncard : Int) := by
  have hup := WilliamsonShmoys.planar_drawing_edge_count_upper_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c M hV hM
  have hlo := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c M hV hM hmax
  have he : (M.edgeSet.ncard : Int) =
      (3 : Int) * (Fintype.card V : Int) - 6 := by omega
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩
  · have hf : ((2 * Fintype.card V - 4 : Nat) : Int) =
        2 * (Fintype.card V : Int) - 4 := by omega
    omega
  · have hf : ((2 * Fintype.card V - 4 : Nat) : Int) =
        2 * (Fintype.card V : Int) - 4 := by omega
    omega