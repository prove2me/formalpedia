-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_has_drawable_edge_extension_for_connected_extension_b575eb0b_092c_4d6e_a44b_f1a402a11573
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:49:11.415066+00:00
-- url     : https://prove2.me/submissions/61ff13be-0763-4de8-9434-b50fad30bf64

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (K : SimpleGraph V),
        HasPlanarDrawingOn K →
        ¬ K.Connected →
        ∃ N : SimpleGraph V,
          K ≤ N ∧ K ≠ N ∧ HasPlanarDrawingOn N) := by
  intro h
  let K : SimpleGraph Empty := ⊥
  have hDraw : HasPlanarDrawingOn K := by
    refine ⟨(fun v : Empty => nomatch v), (fun u v t => nomatch u), ?_, ?_, ?_⟩
    · intro a b hab
      exact Empty.elim a
    · intro u v huv hadj
      exact Empty.elim u
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      exact Empty.elim u
  have hDisconnected : ¬ K.Connected := by
    intro hc
    have hn : Nonempty Empty := hc.2
    exact hn.elim (fun x => nomatch x)
  obtain ⟨N, hle, hStrict, hNDraw⟩ :=
    h (V := Empty) K hDraw hDisconnected
  have hEq : N = K := by
    apply SimpleGraph.ext
    funext u v
    exact Empty.elim u
  exact hStrict hEq.symm