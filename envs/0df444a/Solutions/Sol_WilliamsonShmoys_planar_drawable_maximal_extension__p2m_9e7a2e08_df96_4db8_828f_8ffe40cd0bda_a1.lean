-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_maximal_extension__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:47:16.020484+00:00
-- url     : https://prove2.me/submissions/f6f2bde7-c222-4908-8061-3e58b9d0b631

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawable_extension_max_edge_cardinality__p2m_28aa14c5_09a5_4ce3_a139_0c8dcdfcfd9a_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (dW : DecidableRel W.Adj)
    (hW : HasPlanarDrawingOn W) :
    ∃ (T : SimpleGraph V) (dT : DecidableRel T.Adj),
      HasPlanarDrawingOn T ∧
      (letI : DecidableRel W.Adj := dW
       letI : DecidableRel T.Adj := dT
       W.edgeFinset ⊆ T.edgeFinset) ∧
      (∀ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
        HasPlanarDrawingOn U →
        (letI : DecidableRel T.Adj := dT
         letI : DecidableRel U.Adj := dU
         T.edgeFinset ⊆ U.edgeFinset) →
        (letI : DecidableRel T.Adj := dT
         letI : DecidableRel U.Adj := dU
         U.edgeFinset ⊆ T.edgeFinset)) := by
  classical
  obtain ⟨T, dT, hT, hWT, hmax⟩ :=
    WilliamsonShmoys.planar_drawable_extension_max_edge_cardinality__p2m_28aa14c5_09a5_4ce3_a139_0c8dcdfcfd9a_a2
      W dW hW
  refine ⟨T, dT, hT, hWT, ?_⟩
  intro U dU hU hTU
  have hWU :
      (letI : DecidableRel W.Adj := dW
       letI : DecidableRel U.Adj := dU
       W.edgeFinset ⊆ U.edgeFinset) := hWT.trans hTU
  have hcard := hmax U dU hU hWU
  have heq :
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset = U.edgeFinset) := by
    exact Finset.eq_of_subset_of_card_le hTU hcard
  rw [← heq]