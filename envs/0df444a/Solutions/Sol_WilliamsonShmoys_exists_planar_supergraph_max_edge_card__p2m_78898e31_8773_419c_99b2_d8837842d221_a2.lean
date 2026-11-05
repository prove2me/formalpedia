-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_max_edge_card__p2m_78898e31_8773_419c_99b2_d8837842d221_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:21:01.033669+00:00
-- url     : https://prove2.me/submissions/e30ba5e9-c7b9-4b82-a11c-df4fedcfa5d8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, L ≤ N → HasPlanarDrawingOn N →
        N.edgeSet.ncard ≤ M.edgeSet.ncard) := by
  classical
  let s : Set (SimpleGraph V) := {N | L ≤ N ∧ HasPlanarDrawingOn N}
  have hsne : s.Nonempty := ⟨L, by simp [s, hL]⟩
  have hsfinite : s.Finite := s.toFinite
  obtain ⟨M, hMs, hmax⟩ :=
    Set.exists_max_image s (fun N : SimpleGraph V => N.edgeSet.ncard) hsfinite hsne
  have hMs' : L ≤ M ∧ HasPlanarDrawingOn M := by simpa [s] using hMs
  refine ⟨M, hMs'.1, hMs'.2, ?_⟩
  intro N hLN hN
  exact hmax N (by simpa [s] using (show L ≤ N ∧ HasPlanarDrawingOn N from ⟨hLN, hN⟩))
