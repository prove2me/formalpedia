-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_fd4411d1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:28:51.971832+00:00
-- url     : https://prove2.me/submissions/478928ae-5dfe-4bae-833d-68985ec049d7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
  classical
  let S : Set (SimpleGraph V) := {G | K ≤ G ∧ HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨H, hHmax⟩ := hSfinite.exists_maximal hSnonempty
  have hHmem : K ≤ H ∧ HasPlanarDrawingOn H := hHmax.1
  refine ⟨H, hHmem.1, hHmem.2, ?_⟩
  intro J hHJ hJ
  exact hHmax.2 ⟨hHmem.1.trans hHJ, hJ⟩ hHJ