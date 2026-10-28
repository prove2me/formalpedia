-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_finite_edge_max_20261027
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T03:46:05.192635+00:00
-- url     : https://prove2.me/submissions/0b545f25-47ed-4bc7-90a5-ba8a19e3b0fa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        K ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => K ≤ G ∧ HasPlanarDrawingOn G)).exists_max_image
    (fun G => G.edgeSet.ncard) ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hK⟩⟩
  obtain ⟨hPQ, hQ⟩ : K ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  exact ⟨Q, hPQ, hQ, fun M h1 h2 => hmax M (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)⟩
