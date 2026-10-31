-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:07:06.244167+00:00
-- url     : https://prove2.me/submissions/1d3628c6-1ab4-4cea-be0d-a00bdcad9889

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) (dG : DecidableRel G.Adj)
      (hG : HasPlanarDrawingOn G),
      ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj),
        HasPlanarDrawingOn Q ∧ Q.Connected ∧
          (letI : DecidableRel G.Adj := dG
           letI : DecidableRel Q.Adj := dQ
           G.edgeFinset ⊆ Q.edgeFinset)) := by
  intro h
  letI : Fintype Empty := inferInstance
  letI : LinearOrder Empty := inferInstance
  have hG : HasPlanarDrawingOn (⊥ : SimpleGraph Empty) := by
    refine ⟨(fun x : Empty => nomatch x), (fun x : Empty => nomatch x), ?_, ?_, ?_⟩
    · intro x
      nomatch x
    · intro u
      nomatch u
    · intro u
      nomatch u
  have hEmpty := @h Empty inferInstance inferInstance
    (⊥ : SimpleGraph Empty) (Classical.decRel _) hG
  rcases hEmpty with ⟨Q, dQ, hQ, hconn, hsubset⟩
  rcases hconn.nonempty with ⟨v⟩
  cases v