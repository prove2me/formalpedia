-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_simple_graph_face_incidence_bound__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-03T21:14:45.640123+00:00
-- url     : https://prove2.me/submissions/020bf824-9bb2-4e8d-ad45-75e15608edc0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
        (hconn : K.Connected) (f : ℕ),
        (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
          Fintype.card V + f = K.edgeFinset.card + 2 →
            3 * f ≤ 2 * K.edgeFinset.card)) := by
  intro h
  classical
  let K : SimpleGraph (Fin 1) := ⊥
  have hdraw : HasPlanarDrawingOn K := by
    refine ⟨fun _ => (0, 0), fun _ _ _ => (0, 0), ?_, ?_, ?_⟩
    · intro a b hab
      exact Subsingleton.elim a b
    · intro u v huv hadj
      simp [K] at hadj
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      simp [K] at hadj
  have hconn : K.Connected := SimpleGraph.Connected.of_subsingleton
  have hempty : ∀ [i : Fintype K.edgeSet], @SimpleGraph.edgeFinset (Fin 1) K i = ∅ := by
    intro i
    apply SimpleGraph.edgeFinset_eq_empty.mpr
    rfl
  have hbad := h (V := Fin 1) K hdraw hconn 1
  simp only [hempty, Finset.card_empty, Fintype.card_fin] at hbad
  norm_num at hbad
