-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_24784cbb_b8f6_4e91_b5ba_b51ad6a651ca_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:00:47.645827+00:00
-- url     : https://prove2.me/submissions/377e7f92-955b-47e4-8731-810f56e02852

import Mathlib

open SimpleGraph

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V -> Prop) (X : SimpleGraph V) (hX : P X) :
    Exists fun Y : SimpleGraph V => LE.le X Y /\ P Y /\ forall Z : SimpleGraph V, LE.le Y Z -> P Z -> Y = Z := by
  classical
  let admissible : Set (SimpleGraph V) := {Y | X <= Y /\ P Y}
  have hfinite : admissible.Finite := Set.toFinite admissible
  have hnonempty : admissible.Nonempty := ⟨X, by simp [admissible, hX]⟩
  obtain ⟨Y, hY, hmax⟩ := hfinite.exists_maximal hnonempty
  refine ⟨Y, hY.1, hY.2, ?_⟩
  intro Z hYZ hPZ
  have hZ : Z ∈ admissible := ⟨hY.1.trans hYZ, hPZ⟩
  have hZY : Z <= Y := hmax hZ hYZ
  exact le_antisymm hYZ hZY