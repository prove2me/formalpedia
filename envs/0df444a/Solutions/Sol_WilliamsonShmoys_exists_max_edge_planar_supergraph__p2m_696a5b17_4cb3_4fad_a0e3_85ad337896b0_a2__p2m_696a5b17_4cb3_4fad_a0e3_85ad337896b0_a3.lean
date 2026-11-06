-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_edge_planar_supergraph__p2m_696a5b17_4cb3_4fad_a0e3_85ad337896b0_a2__p2m_696a5b17_4cb3_4fad_a0e3_85ad337896b0_a3
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:58:14.840222+00:00
-- url     : https://prove2.me/submissions/00161157-6871-4ec3-add7-8fd9e200009d

-- ID: 57a5d2a0-6002-4d73-ad7c-0d5b1a326044 | NAME: WilliamsonShmoys.exists_max_edge_planar_supergraph__p2m_696a5b17_4cb3_4fad_a0e3_85ad337896b0_a2__p2m_696a5b17_4cb3_4fad_a0e3_85ad337896b0_a3 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, H.edgeSet ⊆ L.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  let s : Set (SimpleGraph V) := {N | H ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N}
  have hsne : s.Nonempty := ⟨H, by simp [s, hDraw]⟩
  have hsfinite : s.Finite := s.toFinite
  obtain ⟨K, hKs, hmax⟩ :=
    Set.exists_max_image s (fun N : SimpleGraph V => N.edgeSet.ncard) hsfinite hsne
  have hKs' : H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by simpa [s] using hKs
  refine ⟨K, SimpleGraph.edgeSet_subset_edgeSet.mpr hKs'.1, hKs'.2, ?_⟩
  intro L hHL hL
  exact hmax L (by
    simpa [s] using (show H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L from
      ⟨SimpleGraph.edgeSet_subset_edgeSet.mp hHL, hL⟩))
