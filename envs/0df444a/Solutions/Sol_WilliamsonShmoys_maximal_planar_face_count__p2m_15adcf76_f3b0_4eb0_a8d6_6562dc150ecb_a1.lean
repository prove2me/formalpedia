-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count__p2m_15adcf76_f3b0_4eb0_a8d6_6562dc150ecb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:25:11.526211+00:00
-- url     : https://prove2.me/submissions/6e7875fb-f1b6-4587-af07-ded44aa9aba9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_94636b31_2f9e_4256_93d0_7a9950cdcd71_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_94636b31_2f9e_4256_93d0_7a9950cdcd71_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      HasPlanarDrawingOn K → H ≤ K → K ≤ H) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      3 * f = 2 * H.edgeFinset.card := by
  obtain ⟨K, hHK, hK, hKmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_94636b31_2f9e_4256_93d0_7a9950cdcd71_a1
      H hH hcard
  letI : DecidableRel K.Adj := Classical.decRel _
  have hKH : K ≤ H := hmax K hK hHK
  have hKE :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_94636b31_2f9e_4256_93d0_7a9950cdcd71_a1
      K hK hcard hKmax
  have hE : H.edgeFinset.card = K.edgeFinset.card := by
    apply Nat.le_antisymm
    · exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)
    · exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hKH)
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> rw [hE] <;> omega