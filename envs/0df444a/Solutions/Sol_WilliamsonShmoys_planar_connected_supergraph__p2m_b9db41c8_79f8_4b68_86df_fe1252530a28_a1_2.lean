-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_supergraph__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:09.018747+00:00
-- url     : https://prove2.me/submissions/a9700a2c-a7e2-4902-9d63-c0626f8c572e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H),
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K) := by
  intro h
  let H : SimpleGraph Empty := ⊤
  have hH : HasPlanarDrawingOn H := by
    refine ⟨(fun _ : Empty => ((0 : ℝ), (0 : ℝ))),
      (fun u _ _ => u.elim), ?_, ?_, ?_⟩
    · intro u v huv
      cases u
    · intro u v huv hadj
      cases u
    · intro u v x y huv hxy hadj1 hadj2 hne t ht s hs heq
      cases u
  obtain ⟨K, hHK, hK, hplanar⟩ := h (V := Empty) H hH
  exact hK.nonempty.elim (fun v => nomatch v)