-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_connected_supergraph__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:06.015976+00:00
-- url     : https://prove2.me/submissions/ddfcd905-09e4-4b12-b172-b97613f46075

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V), HasPlanarDrawingOn T →
      ∃ U : SimpleGraph V, T ≤ U ∧ U.Connected ∧ HasPlanarDrawingOn U) := by
  intro h
  have hplanar : HasPlanarDrawingOn (⊥ : SimpleGraph PEmpty) := by
    unfold HasPlanarDrawingOn
    refine ⟨(fun x : PEmpty => x.elim), (fun u _ _ => u.elim), ?_⟩
    constructor
    · intro x
      exact x.elim
    · simp
  obtain ⟨U, _hTU, hUconn, _hUplanar⟩ :=
    h (V := PEmpty) (T := (⊥ : SimpleGraph PEmpty)) hplanar
  exact PEmpty.elim (Classical.choice hUconn.nonempty)