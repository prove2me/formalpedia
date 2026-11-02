-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e972185b_4990_47b3_b33a_686d33f273ec_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:29:34.224205+00:00
-- url     : https://prove2.me/submissions/b7c6b732-a0d5-4195-8ac7-0a165891202c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count__p2m_8ea6d6e0_f206_47b7_9e0b_83b7a69a6862_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
      (∀ u v, H.Adj u v → K.Adj u v) →
      ∀ u v, K.Adj u v → H.Adj u v) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      3 * Fintype.card V ≤ H.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨K, hK, hHK, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_8ea6d6e0_f206_47b7_9e0b_83b7a69a6862_a2
      H hV hH
  have hKH : ∀ u v, K.Adj u v → H.Adj u v := hmax K hK hHK
  have hEq : K = H := by
    ext u v
    exact ⟨hKH u v, hHK u v⟩
  have hcards : K.edgeFinset.card = H.edgeFinset.card :=
    congrArg (fun G : SimpleGraph V => G.edgeFinset.card) hEq
  omega