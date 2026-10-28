-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_supergraph_max_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:09:18.607609+00:00
-- url     : https://prove2.me/submissions/124921e3-51c4-44cb-bffa-daac38b51d23

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, H ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        Nat.card {e : Sym2 V // e ∈ L.edgeSet} ≤ Nat.card {e : Sym2 V // e ∈ K.edgeSet} := by
  obtain ⟨K, ⟨hHK, hK⟩, hmax⟩ := Set.exists_max_image
    {G : SimpleGraph V | H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
    (fun G => Nat.card {e : Sym2 V // e ∈ G.edgeSet}) (Set.toFinite _) ⟨H, le_rfl, hdraw⟩
  exact ⟨K, hHK, hK, fun L hL hLd => hmax L ⟨hL, hLd⟩⟩
