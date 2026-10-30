-- Prove2me | solution 2 for WilliamsonShmoys_maximal_planar_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T10:15:06.977968+00:00
-- url     : https://prove2.me/submissions/96239766-5b73-4cd4-a032-44e31661b022

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_c3c27980_9f1d_4b26_ac26_4100a7115914

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_edge_bound_c3c27980_9f1d_4b26_ac26_4100a7115914
  | (apply _root_.WilliamsonShmoys.maximal_planar_edge_bound_c3c27980_9f1d_4b26_ac26_4100a7115914 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_edge_bound_c3c27980_9f1d_4b26_ac26_4100a7115914 <;> assumption)
