-- Prove2me | solution 2 for WilliamsonShmoys.planarDrawingOn_add_edge_across_components
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:11:22.584268+00:00
-- url     : https://prove2.me/submissions/94369e77-f1e3-4183-9d1e-f3b3235e3e97

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (J : SimpleGraph V),
        HasPlanarDrawingOn J →
        ¬ J.Connected →
        ∃ u v : V, u ≠ v ∧ ¬ J.Adj u v ∧
          ∃ K : SimpleGraph V,
            J ≤ K ∧ K.Adj u v ∧ HasPlanarDrawingOn K) := by
  intro h
  let J : SimpleGraph Empty := ⊥
  have hDraw : HasPlanarDrawingOn J := by
    refine ⟨(fun v : Empty => nomatch v), (fun u v t => nomatch u), ?_, ?_, ?_⟩
    · intro a b hab
      exact Empty.elim a
    · intro u v huv hadj
      exact Empty.elim u
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      exact Empty.elim u
  have hNotConnected : ¬ J.Connected := by
    intro hConnected
    exact hConnected.2.elim (fun v => nomatch v)
  obtain ⟨u, v, huv, hnot, K, hJK, hKuv, hKDraw⟩ :=
    h (V := Empty) J hDraw hNotConnected
  exact Empty.elim u