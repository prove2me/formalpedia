-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_add_edge_between_components_a1fa2dac
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:43:31.808983+00:00
-- url     : https://prove2.me/submissions/ed7f4e51-b745-4f6f-81f6-426a7bf4e15c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V)
      (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
      (hDisconnected : ¬ G.Connected),
      ∃ K : SimpleGraph V,
        G ≤ K ∧ G ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K) := by
  intro h
  let G : SimpleGraph (Fin 0) := ⊥
  have hDisconnected : ¬ G.Connected := by
    intro hc
    exact Fin.elim0 (Classical.choice hc.nonempty)
  have hG : WilliamsonShmoys.HasPlanarDrawingOn G := by
    refine ⟨(fun x : Fin 0 => Fin.elim0 x),
      (fun x : Fin 0 => fun y : Fin 0 => fun t : ℝ => Fin.elim0 x), ?_⟩
    constructor
    · intro x y
      exact Fin.elim0 x
    · constructor
      · intro u v huv
        exact Fin.elim0 u
      · intro u v x y huv hxy hadj hxyAdj hne t ht s hs heq
        exact Fin.elim0 u
  obtain ⟨K, hGK, hneq, _hK⟩ :=
    h (V := Fin 0) G hG hDisconnected
  have hKG : K = G := by
    apply SimpleGraph.ext
    funext u v
    exact Fin.elim0 u
  exact hneq hKG.symm
