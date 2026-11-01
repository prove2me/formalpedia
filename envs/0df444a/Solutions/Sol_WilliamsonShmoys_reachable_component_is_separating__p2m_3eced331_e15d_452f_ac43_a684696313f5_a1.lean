-- Prove2me | solution 1 for WilliamsonShmoys.reachable_component_is_separating__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:16:06.582804+00:00
-- url     : https://prove2.me/submissions/23886977-e640-450a-ac1d-60c0f5db9c51

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V)
    (hdisconnected : ¬ G.Reachable u v) :
    ∃ A : Set V, u ∈ A ∧ v ∉ A ∧
      ∀ a b, a ∈ A → b ∉ A → ¬ G.Adj a b := by
  refine ⟨{w | G.Reachable u w}, ?_, ?_, ?_⟩
  · simp
  · simpa using hdisconnected
  · intro a b ha hb hab
    apply hb
    exact SimpleGraph.Reachable.trans ha hab.reachable