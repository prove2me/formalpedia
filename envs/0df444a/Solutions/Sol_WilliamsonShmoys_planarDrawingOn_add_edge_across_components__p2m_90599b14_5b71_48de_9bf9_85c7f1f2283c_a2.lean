-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_add_edge_across_components__p2m_90599b14_5b71_48de_9bf9_85c7f1f2283c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:19:27.229993+00:00
-- url     : https://prove2.me/submissions/afd8c275-c958-4981-9c5b-d6cf79f7401f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_components_exact
import Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_strict_extension
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count_core


open WilliamsonShmoys

set_option autoImplicit false

theorem ds_aux {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hD : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hd : ¬ G.Connected) : G.edgeSet.ncard + 6 < 3 * Fintype.card V := by
  classical
  by_cases h2 : 2 ≤ G.edgeSet.ncard
  · have hb := WilliamsonShmoys.planar_drawing_edge_bound_components_exact G hV hD h2
    have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have hpre : ¬ G.Preconnected := fun h => hd ⟨h⟩
    unfold SimpleGraph.Preconnected at hpre
    push_neg at hpre
    obtain ⟨u, v, huv⟩ := hpre
    have hne2 : G.connectedComponentMk u ≠ G.connectedComponentMk v := by
      intro h; exact huv (SimpleGraph.ConnectedComponent.eq.mp h)
    haveI : Finite G.ConnectedComponent := inferInstance
    have h1 : 1 < Nat.card G.ConnectedComponent :=
      Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨_, _, hne2⟩⟩
    omega
  · have : 3 ≤ Fintype.card V := hV
    omega

theorem conn_aux {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hD : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hE : G.edgeSet.ncard + 6 = 3 * Fintype.card V) : G.Connected := by
  by_contra hd
  have := ds_aux G hV hD hd
  omega

theorem cc_aux {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hD : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by
  classical
  obtain ⟨H, h1, h2, h3⟩ := WilliamsonShmoys.exists_connected_supergraph_of_strict_extension G
    WilliamsonShmoys.HasPlanarDrawingOn hD (by
      intro K hK hPK hnc
      have hs := ds_aux K hV hPK hnc
      obtain ⟨T, hle, hT, hc⟩ := WilliamsonShmoys.planar_graph_has_triangulated_supergraph K hV hPK
      refine ⟨T, lt_of_le_of_ne hle ?_, hT⟩
      intro h; rw [← h] at hc; omega)
  exact ⟨H, h1, h2, h3⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hNotConnected : ¬ J.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ u v : V, u ≠ v ∧ ¬ J.Adj u v ∧
      ∃ K : SimpleGraph V,
        J ≤ K ∧ K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  classical
  have hs := ds_aux J hCard hDraw hNotConnected
  obtain ⟨T, hle, hT, hc⟩ := WilliamsonShmoys.planar_graph_has_triangulated_supergraph J hCard hDraw
  have hn : ¬ T ≤ J := by
    intro h
    have := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h) (Set.toFinite _)
    omega
  have : ∃ u v, T.Adj u v ∧ ¬ J.Adj u v := by
    by_contra hh
    push_neg at hh
    exact hn (fun u v h => hh u v h)
  obtain ⟨u, v, h1, h2⟩ := this
  exact ⟨u, v, T.ne_of_adj h1, h2, T, hle, h1, hT⟩
