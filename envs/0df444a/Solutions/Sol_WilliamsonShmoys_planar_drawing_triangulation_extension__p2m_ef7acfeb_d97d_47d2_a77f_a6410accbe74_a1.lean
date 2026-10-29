-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ef7acfeb_d97d_47d2_a77f_a6410accbe74_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:25:02.05106+00:00
-- url     : https://prove2.me/submissions/7b51c568-58d5-4002-8d50-adab4815aea5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a1__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter
      (fun K : SimpleGraph V =>
        G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K)
  have hSne : S.Nonempty := by
    refine ⟨G, ?_⟩
    simp [S, hG]
  obtain ⟨H, hHm, hbest⟩ :=
    Finset.exists_max_image S (fun K : SimpleGraph V => K.edgeFinset.card) hSne
  have hH : WilliamsonShmoys.HasPlanarDrawingOn H :=
    (Finset.mem_filter.mp hHm).2.2
  have hGH : G ≤ H := (Finset.mem_filter.mp hHm).2.1
  have hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by
    intro K hHK hK
    by_contra hKH
    have hKm : K ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ K, ⟨hGH.trans hHK, hK⟩⟩
    have hstrict : H.edgeFinset ⊂ K.edgeFinset := by
      apply SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr
      exact ⟨hHK, hKH⟩
    have hcardlt := Finset.card_lt_card hstrict
    have hcardle := hbest K hKm
    omega
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a1__p2m_b76a54ef_1c48_4c54_85f5_81d888cceed1_a2
      H hV hH hmax
  exact ⟨H, hGH, hcount, hH⟩