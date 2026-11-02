-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:04:06.247396+00:00
-- url     : https://prove2.me/submissions/815f9226-3f35-4891-a022-31b03dec85ec

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (K : SimpleGraph V)
        (hK : WilliamsonShmoys.HasPlanarDrawingOn K),
        ∃ H : SimpleGraph V,
          K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H) := by
  intro h
  have hDrawing : WilliamsonShmoys.HasPlanarDrawingOn (⊥ : SimpleGraph PEmpty) := by
    unfold WilliamsonShmoys.HasPlanarDrawingOn
    refine ⟨(fun v => PEmpty.elim v), (fun _ _ _ => (0, 0)), ?_, ?_, ?_⟩
    · intro u v huv
      exact PEmpty.elim u
    · intro u v huv hadj
      exact PEmpty.elim u
    · intro u v x y huv hxy hadj hadj' hne t ht s hs hEq
      exact PEmpty.elim u
  obtain ⟨H, hle, hConnected, hPlanar⟩ :=
    h (V := PEmpty) (K := (⊥ : SimpleGraph PEmpty)) hDrawing
  exact PEmpty.elim (Classical.choice hConnected.nonempty)