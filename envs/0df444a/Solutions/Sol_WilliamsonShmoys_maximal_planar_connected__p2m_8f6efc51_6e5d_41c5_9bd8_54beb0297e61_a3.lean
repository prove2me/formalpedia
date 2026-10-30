-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_connected__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:41:38.477885+00:00
-- url     : https://prove2.me/submissions/508eb9ae-c48c-4408-902f-dc0f67974745

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H),
    H.Connected) := by
  intro h
  let H : SimpleGraph Empty := ⊥
  have hH : WilliamsonShmoys.HasPlanarDrawingOn H := by
    refine ⟨(fun x : Empty => x.elim), (fun x y _ => x.elim), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x y _
      exact x.elim
    · intro u v _ _
      exact u.elim
    · intro u v x y _ _ _ _ _
      exact u.elim
  have hMaximal : ∀ K : SimpleGraph Empty, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
    intro K hHK hK
    ext u v
    exact u.elim
  have hconn := h (H := H) hH hMaximal
  rcases hconn.nonempty with ⟨v⟩
  exact v.elim