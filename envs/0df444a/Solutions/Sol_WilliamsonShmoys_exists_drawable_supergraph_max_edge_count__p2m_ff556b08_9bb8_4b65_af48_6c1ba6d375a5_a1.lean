-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_supergraph_max_edge_count__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:49:42.107989+00:00
-- url     : https://prove2.me/submissions/e7a277ab-25cc-42c0-8000-2137f011d86e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard) := by
  classical
  let eligible : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun K => G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K)
  have hGeligible : G ∈ eligible := by
    simp [eligible, hG]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image eligible (fun K => K.edgeSet.ncard) ⟨G, hGeligible⟩
  have hKprops : G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
    simpa [eligible] using hKmem
  refine ⟨K, hKprops.1, hKprops.2, ?_⟩
  intro L hKL hLdraw
  apply hKmax L
  simp [eligible, hKprops.1.trans hKL, hLdraw]