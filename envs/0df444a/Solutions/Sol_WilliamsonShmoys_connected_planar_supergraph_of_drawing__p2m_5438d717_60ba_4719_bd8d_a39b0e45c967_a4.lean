-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_supergraph_of_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:15:24.909968+00:00
-- url     : https://prove2.me/submissions/66997b65-f447-4956-98d9-a69cfd1837e2

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
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  have hB := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc N hCard hN
  obtain ⟨Tz, hlez, hTz, hcz⟩ := WilliamsonShmoys.planar_graph_has_triangulated_supergraph N hCard hN
  have hconTz : Tz.Connected := conn_aux Tz hCard hTz (by omega)
  obtain ⟨fz, hfz3, hfze⟩ := WilliamsonShmoys.connected_planar_drawing_euler_face_count_core Tz hCard hconTz hTz
  obtain ⟨Hc, hGc, hHc, hHconn⟩ := cc_aux N hCard hN
  have hcc : N.edgeSet.ncard ≤ Hc.edgeSet.ncard := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGc) (Set.toFinite _)
  first
  | omega
  | (by_contra hd; have := ds_aux N hCard hN hd; omega)
  | (refine ⟨Tz, ?_⟩; and_intros <;> first | exact hlez | exact hTz | exact SimpleGraph.edgeSet_mono hlez | (intro u v hh; exact hlez hh) | omega | exact hconTz | (refine ⟨fz, ?_⟩; and_intros <;> omega))
  | (refine ⟨Hc, ?_⟩; and_intros <;> first | exact hGc | exact hHc | exact hHconn | exact SimpleGraph.edgeSet_mono hGc | (intro u v hh; exact hGc hh) | omega | exact hcc | (refine ⟨fz, ?_⟩; and_intros <;> omega))
  | (refine ⟨fz, ?_⟩; and_intros <;> omega)
  | (and_intros <;> first | exact hGc | exact hHc | exact hHconn | exact SimpleGraph.edgeSet_mono hGc | (intro u v hh; exact hGc hh) | omega | exact hcc | omega)
  | (refine ⟨2 * Fintype.card V - 4, ?_⟩; and_intros <;> omega)
  | (refine ⟨3 * Fintype.card V - 6, 2 * Fintype.card V - 4, ?_⟩; and_intros <;> omega)
