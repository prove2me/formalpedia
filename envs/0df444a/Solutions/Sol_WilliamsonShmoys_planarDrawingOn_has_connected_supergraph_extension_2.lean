-- Prove2me | solution 2 for WilliamsonShmoys.planarDrawingOn_has_connected_supergraph_extension
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:01:09.094993+00:00
-- url     : https://prove2.me/submissions/0350c3e2-06d8-4ed9-98fc-4150f0faa187

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (J : SimpleGraph V),
        HasPlanarDrawingOn J →
        ∃ M : SimpleGraph V,
          J ≤ M ∧ HasPlanarDrawingOn M ∧ M.Connected) := by
  intro h
  let J : SimpleGraph Empty := ⊤
  have hDraw : HasPlanarDrawingOn J := by
    refine ⟨(fun v : Empty => nomatch v), (fun u v t => nomatch u), ?_, ?_, ?_⟩
    · intro a b hab
      exact Empty.elim a
    · intro u v huv hadj
      exact Empty.elim u
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      exact Empty.elim u
  obtain ⟨M, hJM, hMDraw, hConnected⟩ := h (V := Empty) J hDraw
  exact hConnected.2.elim (fun v => nomatch v)