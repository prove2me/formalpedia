-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:44:23.107196+00:00
-- url     : https://prove2.me/submissions/808fdd68-8b65-4081-a05b-6aea17ab24f7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_maximal_extension_repair2_finite_candidates
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_maximal_extension_repair2_finite_maximal

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      G ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ M : SimpleGraph V, N ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ N := by
  classical
  let S : Set (SimpleGraph V) :=
    {M | G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M}
  have hS : S.Nonempty := ⟨G, le_rfl, hG⟩
  have hfinite : S.Finite :=
    WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2_finite_candidates G
  obtain ⟨N, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_on_maximal_extension_repair2_finite_maximal S hS hfinite
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro M hNM hM
  have hMmem : M ∈ S := ⟨le_trans hN.1 hNM, hM⟩
  exact hmax M hMmem hNM