-- Prove2me | solution 1 for WilliamsonShmoys.strict_added_edge_finset__p2m_a28e5ee4_bf60_4e7a_aa04_8ab47cd06895_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:51:06.777249+00:00
-- url     : https://prove2.me/submissions/41b05707-910b-48fe-a985-70a296f4e07a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V) [DecidableRel K.Adj] [DecidableRel L.Adj]
    (u v : V) (huv : u < v) (hnonadj : ¬ K.Adj u v)
    (hLrel : ∀ a b, L.Adj a b ↔
      K.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) :
    K.edgeFinset ⊂ L.edgeFinset := by
  rw [SimpleGraph.edgeFinset_ssubset_edgeFinset, lt_iff_le_not_ge]
  constructor
  · intro a b hab
    exact (hLrel a b).2 (Or.inl hab)
  · intro hLleK
    have hLuv : L.Adj u v :=
      (hLrel u v).2 (Or.inr (Or.inl (by constructor <;> rfl)))
    exact hnonadj (hLleK hLuv)