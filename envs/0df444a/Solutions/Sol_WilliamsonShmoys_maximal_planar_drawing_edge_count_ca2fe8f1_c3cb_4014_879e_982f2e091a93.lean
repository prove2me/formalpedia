-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_ca2fe8f1_c3cb_4014_879e_982f2e091a93
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:33:06.669982+00:00
-- url     : https://prove2.me/submissions/674b304e-b1c8-40dd-bc75-f5a405d5c6e0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_with_six_offset
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_six_offset_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, HasPlanarDrawingOn X →
      (∀ u v, W.Adj u v → X.Adj u v) →
      ∀ u v, X.Adj u v → W.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    W.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_drawing_edge_bound_with_six_offset W hW hCard
  · exact WilliamsonShmoys.maximal_planar_drawing_six_offset_lower_bound W hW hmax hCard