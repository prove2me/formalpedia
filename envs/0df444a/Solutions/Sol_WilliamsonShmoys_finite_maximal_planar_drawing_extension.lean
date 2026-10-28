-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_planar_drawing_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:24:48.827307+00:00
-- url     : https://prove2.me/submissions/65af5852-d727-4222-bc57-c376bbfcf72e

import Mathlib.Order.Preorder.Finite
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M →
          WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨L, hL⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨L, hL.1.1, hL.1.2, ?_⟩
  intro M hLM hM
  have hMmem : M ∈ S := ⟨hL.1.1.trans hLM, hM⟩
  exact le_antisymm (hL.2 hMmem hLM) hLM