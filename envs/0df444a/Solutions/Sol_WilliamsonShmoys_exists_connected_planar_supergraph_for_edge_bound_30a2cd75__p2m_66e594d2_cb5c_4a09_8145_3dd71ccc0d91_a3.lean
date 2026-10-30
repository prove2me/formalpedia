-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_planar_supergraph_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:15:01.881312+00:00
-- url     : https://prove2.me/submissions/f368a29d-2976-457a-8019-1d5a4c91e8de

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_components_exact
import Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_strict_extension
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count_core



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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by
  classical
  have hB := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc G hV hG
  obtain ⟨Tz, hlez, hTz, hcz⟩ := WilliamsonShmoys.planar_graph_has_triangulated_supergraph G hV hG
  have hconTz : Tz.Connected := conn_aux Tz hV hTz (by omega)
  obtain ⟨fz, hfz3, hfze⟩ := WilliamsonShmoys.connected_planar_drawing_euler_face_count_core Tz hV hconTz hTz
  obtain ⟨Hc, hGc, hHc, hHconn⟩ := cc_aux G hV hG
  have hcc : G.edgeSet.ncard ≤ Hc.edgeSet.ncard := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGc) (Set.toFinite _)
  first
  | omega
  | (by_contra hd; have := ds_aux G hV hG hd; omega)
  | (refine ⟨Tz, ?_⟩; and_intros <;> first | exact hlez | exact hTz | exact SimpleGraph.edgeSet_mono hlez | (intro u v hh; exact hlez hh) | omega | exact hconTz | (refine ⟨fz, ?_⟩; and_intros <;> omega))
  | (refine ⟨Hc, ?_⟩; and_intros <;> first | exact hGc | exact hHc | exact hHconn | exact SimpleGraph.edgeSet_mono hGc | (intro u v hh; exact hGc hh) | omega | exact hcc | (refine ⟨fz, ?_⟩; and_intros <;> omega))
  | (refine ⟨fz, ?_⟩; and_intros <;> omega)
  | (and_intros <;> first | exact hGc | exact hHc | exact hHconn | exact SimpleGraph.edgeSet_mono hGc | (intro u v hh; exact hGc hh) | omega | exact hcc | omega)
  | (refine ⟨2 * Fintype.card V - 4, ?_⟩; and_intros <;> omega)
  | (refine ⟨3 * Fintype.card V - 6, 2 * Fintype.card V - 4, ?_⟩; and_intros <;> omega)
