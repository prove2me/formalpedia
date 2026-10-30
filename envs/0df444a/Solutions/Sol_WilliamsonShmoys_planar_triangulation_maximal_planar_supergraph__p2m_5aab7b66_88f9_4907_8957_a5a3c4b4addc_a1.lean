-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_maximal_planar_supergraph__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:31:25.051809+00:00
-- url     : https://prove2.me/submissions/fa8ca56f-f7ae-4a68-9268-6aa09a9e9fa6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V, T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
      (∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W →
        W.edgeSet.ncard ≤ U.edgeSet.ncard) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => T ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨T, ?_⟩
    simp [S, hT]
  obtain ⟨U, hUmem, hUmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeSet.ncard) hS
  refine ⟨U, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hUmem).2.1
  · exact (Finset.mem_filter.mp hUmem).2.2
  · intro W hUW hWplanar
    have hTW : T ≤ W := le_trans (Finset.mem_filter.mp hUmem).2.1 hUW
    have hWmem : W ∈ S := by simp [S, hTW, hWplanar]
    exact hUmax W hWmem