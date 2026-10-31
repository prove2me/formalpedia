-- Prove2me | solution 2 for WilliamsonShmoys.exists_planar_strict_supergraph_of_not_connected__p2m_bc735298_99fb_476e_aa8d_1e3af7f2e774_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:21:02.100984+00:00
-- url     : https://prove2.me/submissions/94fa5160-892c-478c-97a7-53e7525482f7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V), HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
        K.edgeSet.ncard < L.edgeSet.ncard) := by
  intro h
  let K : SimpleGraph Empty := ⊤
  have hplanar : HasPlanarDrawingOn K := by
    refine ⟨(fun x : Empty => x.elim), (fun u : Empty => u.elim), ?_, ?_, ?_⟩
    · intro x y hxy
      cases x
    · intro u
      cases u
    · intro u
      cases u
  have hnot : ¬ K.Connected := by
    simp [K, SimpleGraph.connected_iff]
  obtain ⟨L, hKL, hLplanar, hlt⟩ :=
    h (V := Empty) K hplanar hnot
  have hEq : L = K := by
    ext u v
    cases u
  rw [hEq] at hlt
  exact (Nat.lt_irrefl _) hlt