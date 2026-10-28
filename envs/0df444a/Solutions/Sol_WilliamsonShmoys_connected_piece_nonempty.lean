-- Prove2me | solution 1 for WilliamsonShmoys.connected_piece_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:40:04.282675+00:00
-- url     : https://prove2.me/submissions/aa44a039-a553-4757-bfbd-2a85934ef9e1

import Mathlib
theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V)
    (hconn : (G.induce (↑S : Set V)).Connected) :
    0 < S.card := by
  obtain ⟨⟨v, hv⟩⟩ := hconn.nonempty
  exact Finset.card_pos.mpr ⟨v, hv⟩
