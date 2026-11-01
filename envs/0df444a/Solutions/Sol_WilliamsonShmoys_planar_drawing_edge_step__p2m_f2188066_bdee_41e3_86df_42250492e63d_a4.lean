-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_step__p2m_f2188066_bdee_41e3_86df_42250492e63d_a4
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:26:50.532407+00:00
-- url     : https://prove2.me/submissions/ef85d19e-0d8b-4593-85d8-e7dbe56927e6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V),
      HasPlanarDrawingOn G →
      ¬ G.Connected →
      ∃ H : SimpleGraph V,
        G.edgeSet ⊂ H.edgeSet ∧ HasPlanarDrawingOn H) := by
  intro h
  let V := Empty
  let G : SimpleGraph V := ⊥
  have hdraw : HasPlanarDrawingOn G := by
    refine ⟨(fun x : V => nomatch x), (fun u v t => nomatch u), ?_, ?_⟩
    · intro x y hxy
      exact nomatch x
    · constructor
      · intro u v huv hadj
        exact nomatch u
      · intro u v x y huv hxy hadjuv hadjxy hne t ht s hs heq
        exact nomatch u
  have hdisconnected : ¬ G.Connected := by
    intro hc
    exact hc.nonempty.elim (fun x => nomatch x)
  obtain ⟨H, hstrict, _⟩ := h (V := V) G hdraw hdisconnected
  have hH : H = (⊥ : SimpleGraph V) := Subsingleton.elim _ _
  subst H
  have hG : G = (⊥ : SimpleGraph V) := Subsingleton.elim _ _
  subst G
  simp at hstrict