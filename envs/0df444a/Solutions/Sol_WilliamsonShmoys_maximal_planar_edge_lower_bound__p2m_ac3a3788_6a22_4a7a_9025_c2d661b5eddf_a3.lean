-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ac3a3788_6a22_4a7a_9025_c2d661b5eddf_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:15:26.120265+00:00
-- url     : https://prove2.me/submissions/8a47cbf1-5f18-43d8-a106-45eaa2230ab3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_2ae65a7c_57f2_4cef_ba44_e42518b858bb_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (dW : DecidableRel W.Adj)
    (hW : HasPlanarDrawingOn W)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (X : SimpleGraph V) (dX : DecidableRel X.Adj),
      HasPlanarDrawingOn X →
      (letI : DecidableRel W.Adj := dW
       letI : DecidableRel X.Adj := dX
       W.edgeFinset ⊆ X.edgeFinset) →
      (letI : DecidableRel W.Adj := dW
       letI : DecidableRel X.Adj := dX
       X.edgeFinset ⊆ W.edgeFinset)) :
    3 * Fintype.card V - 6 ≤
      (letI : DecidableRel W.Adj := dW; W.edgeFinset.card) := by
  obtain ⟨T, dT, hT, hWT, hTcard⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_2ae65a7c_57f2_4cef_ba44_e42518b858bb_a1
      W dW hW hn
  letI : DecidableRel W.Adj := dW
  letI : DecidableRel T.Adj := dT
  have hTW : T.edgeFinset ⊆ W.edgeFinset := hmax T dT hT hWT
  have hcards : T.edgeFinset.card = W.edgeFinset.card :=
    Nat.le_antisymm (Finset.card_le_card hTW) (Finset.card_le_card hWT)
  calc
    3 * Fintype.card V - 6 = T.edgeFinset.card := hTcard.symm
    _ = W.edgeFinset.card := hcards
    _ ≤ W.edgeFinset.card := le_rfl