-- Prove2me | solution 1 for WilliamsonShmoys.planar_unreachable_vertices_component_cut__p2m_95b2a4a5_f4af_45e5_83a3_0810e97a8978_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:29:28.774628+00:00
-- url     : https://prove2.me/submissions/5dd21cb9-efc4-475e-8cf5-25da821f02aa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (a b : V) (hnotReach : ¬ K.Reachable a b) :
    ∃ P : Set V, P a ∧ ¬ P b ∧
      ∀ u v, K.Adj u v → (P u ↔ P v) := by
  let P : Set V := {v | K.Reachable a v}
  refine ⟨P, ?_, ?_, ?_⟩
  · change K.Reachable a a
    exact SimpleGraph.Reachable.refl a
  · exact hnotReach
  · intro u v huv
    constructor
    · intro hu
      change K.Reachable a u at hu
      change K.Reachable a v
      exact hu.trans (SimpleGraph.Adj.reachable huv)
    · intro hv
      change K.Reachable a v at hv
      change K.Reachable a u
      exact hv.trans (SimpleGraph.Adj.reachable huv.symm)