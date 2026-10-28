-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_one_edge_extension
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:56:37.43264+00:00
-- url     : https://prove2.me/submissions/2747dc54-da7a-4caf-8db9-d981f266ba20

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V),
    HasPlanarDrawingOn K → ¬ K.Connected →
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ K.Reachable u v ∧ H.Adj u v) := by
  intro h
  let V : Type := Empty
  let K : SimpleGraph V := ⊤
  have hDraw : HasPlanarDrawingOn K := by
    refine ⟨(fun x : V => x.elim), (fun u v t => u.elim), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      cases a
    · intro u v huv hAdj
      cases u
    · intro u v x y huv hxy huvAdj hxyAdj hne t ht s hs heq
      cases u
  have hNotConnected : ¬ K.Connected := by
    intro hConnected
    rcases hConnected.nonempty with ⟨x⟩
    exact nomatch x
  have hResult := h (V := V) K hDraw hNotConnected
  rcases hResult with ⟨H, hle, hHDraw, u, v, hNotReachable, hAdj⟩
  exact nomatch u