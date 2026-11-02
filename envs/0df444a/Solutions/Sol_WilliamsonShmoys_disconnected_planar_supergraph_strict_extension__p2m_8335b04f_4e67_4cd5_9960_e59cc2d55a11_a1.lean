-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_supergraph_strict_extension__p2m_8335b04f_4e67_4cd5_9960_e59cc2d55a11_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:02:03.343783+00:00
-- url     : https://prove2.me/submissions/e7431112-f32f-474a-9e72-bb2ff8295abf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V), HasPlanarDrawingOn N → ¬ N.Connected →
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card < K.edgeFinset.card)) := by
  classical
  intro h
  let N : SimpleGraph Empty := ⊥
  have hplanar : HasPlanarDrawingOn N := by
    refine ⟨(fun v : Empty => v.elim), (fun u v t => u.elim), ?_, ?_, ?_⟩
    · intro a b
      cases a
    · intro u v
      cases u
    · intro u v x y
      cases u
  have hdisconnected : ¬ N.Connected := by
    intro hc
    exact Empty.elim (Classical.choice hc.nonempty)
  obtain ⟨K, hsub, hKplanar, hcard⟩ := h (V := Empty) N hplanar hdisconnected
  have hKbot : K = N := Subsingleton.elim _ _
  subst K
  exact (Nat.lt_irrefl _ hcard)