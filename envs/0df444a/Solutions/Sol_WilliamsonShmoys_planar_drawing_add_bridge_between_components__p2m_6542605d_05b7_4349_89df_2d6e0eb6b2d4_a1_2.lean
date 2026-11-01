-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_add_bridge_between_components__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:39:41.963587+00:00
-- url     : https://prove2.me/submissions/8f531f65-2055-4d11-9daa-c3b11aa66753

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (K : SimpleGraph V),
        HasPlanarDrawingOn K →
        ¬ K.Connected →
        ∃ L : SimpleGraph V,
          K.edgeSet ⊆ L.edgeSet ∧
          (∃ u v, ¬ K.Reachable u v ∧ L.Adj u v) ∧
          HasPlanarDrawingOn L) := by
  intro h
  letI : Fintype Empty := inferInstance
  letI : LinearOrder Empty := inferInstance
  have hplanar : HasPlanarDrawingOn (⊤ : SimpleGraph Empty) := by
    refine ⟨(fun x : Empty => Empty.elim x),
      (fun u : Empty => Empty.elim u), ?_, ?_, ?_⟩
    · intro x y _
      exact Empty.elim x
    · intro u v huv hadj
      exact Empty.elim u
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      exact Empty.elim u
  have hdisconnected : ¬ (⊤ : SimpleGraph Empty).Connected := by
    intro hc
    exact hc.nonempty.elim (fun x => Empty.elim x)
  obtain ⟨L, hsub, hex, hLplanar⟩ :=
    h (V := Empty) (⊤ : SimpleGraph Empty) hplanar hdisconnected
  obtain ⟨u, v, hnot, hadj⟩ := hex
  exact Empty.elim u