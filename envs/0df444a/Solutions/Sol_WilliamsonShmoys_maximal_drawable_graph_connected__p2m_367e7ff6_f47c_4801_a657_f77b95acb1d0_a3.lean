-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_connected__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:15:09.77309+00:00
-- url     : https://prove2.me/submissions/69fcf2b8-5fa0-406c-9575-80f07e66b731

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_components_exact
import Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_strict_extension
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count_core


set_option autoImplicit false

open WilliamsonShmoys

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
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.Connected := by
  classical
  have hB := WilliamsonShmoys.planar_edge_count_upper_bound_ef555edc H hCard hDraw
  obtain ⟨Tz, hlez, hTz, hcz⟩ := WilliamsonShmoys.planar_graph_has_triangulated_supergraph H hCard hDraw
  have hconTz : Tz.Connected := conn_aux Tz hCard hTz (by omega)
  obtain ⟨fz, hfz3, hfze⟩ := WilliamsonShmoys.connected_planar_drawing_euler_face_count_core Tz hCard hconTz hTz
  obtain ⟨Hc, hGc, hHc, hHconn⟩ := cc_aux H hCard hDraw
  have hcc : H.edgeSet.ncard ≤ Hc.edgeSet.ncard := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGc) (Set.toFinite _)
  have hcardz : Tz.edgeSet.ncard ≤ H.edgeSet.ncard := by
    first
    | exact hMax Tz hlez hTz
    | exact hMax Tz hTz hlez
    | exact hMax Tz (fun u v hh => hlez hh) hTz
    | exact hMax Tz (fun {u v} hh => hlez hh) hTz
    | exact hMax Tz (fun ⦃u v⦄ hh => hlez hh) hTz
    | exact hMax Tz (SimpleGraph.edgeSet_mono hlez) hTz
    | exact hMax Tz hTz (SimpleGraph.edgeSet_mono hlez)
    | exact hMax Tz hTz (fun u v hh => hlez hh)
    | exact hMax Tz hTz (fun {u v} hh => hlez hh)
    | exact hMax Tz hTz (fun ⦃u v⦄ hh => hlez hh)
    | (have hsub : Tz.edgeSet ⊆ H.edgeSet := by
         first
         | (have h := hMax Tz hlez hTz; exact SimpleGraph.edgeSet_mono h)
         | (have h := hMax Tz hlez hTz; exact h)
         | (have h := hMax Tz hlez hTz; exact le_of_eq (congrArg SimpleGraph.edgeSet h))
         | (have h := hMax Tz hlez hTz; exact le_of_eq (congrArg SimpleGraph.edgeSet h.symm))
         | (have h := hMax Tz hlez hTz; exact SimpleGraph.edgeSet_mono h.le)
         | (have h := hMax Tz hlez hTz; exact SimpleGraph.edgeSet_mono h.symm.le)
         | (have h := hMax Tz hlez hTz; exact le_of_eq h)
         | (have h := hMax Tz hlez hTz; exact h.le)
         | (have h := hMax Tz hlez hTz; exact (fun e => Sym2.ind (fun u v hu => by simpa using h u v (by simpa using hu)) e))
         | (have h := hMax Tz hlez hTz; exact (fun e => Sym2.ind (fun u v hu => by simpa using h (by simpa using hu)) e))
         | (have h := hMax Tz hTz hlez; exact SimpleGraph.edgeSet_mono h)
         | (have h := hMax Tz hTz hlez; exact h)
         | (have h := hMax Tz hTz hlez; exact le_of_eq (congrArg SimpleGraph.edgeSet h))
         | (have h := hMax Tz hTz hlez; exact le_of_eq (congrArg SimpleGraph.edgeSet h.symm))
         | (have h := hMax Tz hTz hlez; exact SimpleGraph.edgeSet_mono h.le)
         | (have h := hMax Tz hTz hlez; exact SimpleGraph.edgeSet_mono h.symm.le)
         | (have h := hMax Tz hTz hlez; exact le_of_eq h)
         | (have h := hMax Tz hTz hlez; exact h.le)
         | (have h := hMax Tz hTz hlez; exact (fun e => Sym2.ind (fun u v hu => by simpa using h u v (by simpa using hu)) e))
         | (have h := hMax Tz hTz hlez; exact (fun e => Sym2.ind (fun u v hu => by simpa using h (by simpa using hu)) e))
         | (have h := hMax Tz (fun u v hh => hlez hh) hTz; exact SimpleGraph.edgeSet_mono h)
         | (have h := hMax Tz (fun u v hh => hlez hh) hTz; exact h)
         | (have h := hMax Tz (fun u v hh => hlez hh) hTz; exact le_of_eq (congrArg SimpleGraph.edgeSet h))
         | (have h := hMax Tz (fun u v hh => hlez hh) hTz; exact le_of_eq (congrArg SimpleGraph.edgeSet h.symm))
         | (have h := hMax Tz (fun u v hh => hlez hh) hTz; exact SimpleGraph.edgeSet_mono h.le)
         | (have h := hMax Tz (fun u v hh => hlez hh) hTz; exact SimpleGraph.edgeSet_mono h.symm.le)
         | (have h := hMax Tz (fun u v hh => hlez hh) hTz; exact le_of_eq h)
         | (have h := hMax Tz (fun u v hh => hlez hh) hTz; exact h.le)
         | (have h := hMax Tz (fun u v hh => hlez hh) hTz; exact (fun e => Sym2.ind (fun u v hu => by simpa using h u v (by simpa using hu)) e))
         | (have h := hMax Tz (fun u v hh => hlez hh) hTz; exact (fun e => Sym2.ind (fun u v hu => by simpa using h (by simpa using hu)) e))
         | (have h := hMax Tz (fun {u v} hh => hlez hh) hTz; exact SimpleGraph.edgeSet_mono h)
         | (have h := hMax Tz (fun {u v} hh => hlez hh) hTz; exact h)
         | (have h := hMax Tz (fun {u v} hh => hlez hh) hTz; exact le_of_eq (congrArg SimpleGraph.edgeSet h))
         | (have h := hMax Tz (fun {u v} hh => hlez hh) hTz; exact le_of_eq (congrArg SimpleGraph.edgeSet h.symm))
         | (have h := hMax Tz (fun {u v} hh => hlez hh) hTz; exact SimpleGraph.edgeSet_mono h.le)
         | (have h := hMax Tz (fun {u v} hh => hlez hh) hTz; exact SimpleGraph.edgeSet_mono h.symm.le)
         | (have h := hMax Tz (fun {u v} hh => hlez hh) hTz; exact le_of_eq h)
         | (have h := hMax Tz (fun {u v} hh => hlez hh) hTz; exact h.le)
         | (have h := hMax Tz (fun {u v} hh => hlez hh) hTz; exact (fun e => Sym2.ind (fun u v hu => by simpa using h u v (by simpa using hu)) e))
         | (have h := hMax Tz (fun {u v} hh => hlez hh) hTz; exact (fun e => Sym2.ind (fun u v hu => by simpa using h (by simpa using hu)) e))
         | (have h := hMax Tz (fun ⦃u v⦄ hh => hlez hh) hTz; exact SimpleGraph.edgeSet_mono h)
         | (have h := hMax Tz (fun ⦃u v⦄ hh => hlez hh) hTz; exact h)
         | (have h := hMax Tz (fun ⦃u v⦄ hh => hlez hh) hTz; exact le_of_eq (congrArg SimpleGraph.edgeSet h))
         | (have h := hMax Tz (fun ⦃u v⦄ hh => hlez hh) hTz; exact le_of_eq (congrArg SimpleGraph.edgeSet h.symm))
         | (have h := hMax Tz (fun ⦃u v⦄ hh => hlez hh) hTz; exact SimpleGraph.edgeSet_mono h.le)
         | (have h := hMax Tz (fun ⦃u v⦄ hh => hlez hh) hTz; exact SimpleGraph.edgeSet_mono h.symm.le)
         | (have h := hMax Tz (fun ⦃u v⦄ hh => hlez hh) hTz; exact le_of_eq h)
         | (have h := hMax Tz (fun ⦃u v⦄ hh => hlez hh) hTz; exact h.le)
         | (have h := hMax Tz (fun ⦃u v⦄ hh => hlez hh) hTz; exact (fun e => Sym2.ind (fun u v hu => by simpa using h u v (by simpa using hu)) e))
         | (have h := hMax Tz (fun ⦃u v⦄ hh => hlez hh) hTz; exact (fun e => Sym2.ind (fun u v hu => by simpa using h (by simpa using hu)) e))
         | (have h := hMax Tz (SimpleGraph.edgeSet_mono hlez) hTz; exact SimpleGraph.edgeSet_mono h)
         | (have h := hMax Tz (SimpleGraph.edgeSet_mono hlez) hTz; exact h)
         | (have h := hMax Tz (SimpleGraph.edgeSet_mono hlez) hTz; exact le_of_eq (congrArg SimpleGraph.edgeSet h))
         | (have h := hMax Tz (SimpleGraph.edgeSet_mono hlez) hTz; exact le_of_eq (congrArg SimpleGraph.edgeSet h.symm))
         | (have h := hMax Tz (SimpleGraph.edgeSet_mono hlez) hTz; exact SimpleGraph.edgeSet_mono h.le)
         | (have h := hMax Tz (SimpleGraph.edgeSet_mono hlez) hTz; exact SimpleGraph.edgeSet_mono h.symm.le)
         | (have h := hMax Tz (SimpleGraph.edgeSet_mono hlez) hTz; exact le_of_eq h)
         | (have h := hMax Tz (SimpleGraph.edgeSet_mono hlez) hTz; exact h.le)
         | (have h := hMax Tz (SimpleGraph.edgeSet_mono hlez) hTz; exact (fun e => Sym2.ind (fun u v hu => by simpa using h u v (by simpa using hu)) e))
         | (have h := hMax Tz (SimpleGraph.edgeSet_mono hlez) hTz; exact (fun e => Sym2.ind (fun u v hu => by simpa using h (by simpa using hu)) e))
         | (have h := hMax Tz hTz (SimpleGraph.edgeSet_mono hlez); exact SimpleGraph.edgeSet_mono h)
         | (have h := hMax Tz hTz (SimpleGraph.edgeSet_mono hlez); exact h)
         | (have h := hMax Tz hTz (SimpleGraph.edgeSet_mono hlez); exact le_of_eq (congrArg SimpleGraph.edgeSet h))
         | (have h := hMax Tz hTz (SimpleGraph.edgeSet_mono hlez); exact le_of_eq (congrArg SimpleGraph.edgeSet h.symm))
         | (have h := hMax Tz hTz (SimpleGraph.edgeSet_mono hlez); exact SimpleGraph.edgeSet_mono h.le)
         | (have h := hMax Tz hTz (SimpleGraph.edgeSet_mono hlez); exact SimpleGraph.edgeSet_mono h.symm.le)
         | (have h := hMax Tz hTz (SimpleGraph.edgeSet_mono hlez); exact le_of_eq h)
         | (have h := hMax Tz hTz (SimpleGraph.edgeSet_mono hlez); exact h.le)
         | (have h := hMax Tz hTz (SimpleGraph.edgeSet_mono hlez); exact (fun e => Sym2.ind (fun u v hu => by simpa using h u v (by simpa using hu)) e))
         | (have h := hMax Tz hTz (SimpleGraph.edgeSet_mono hlez); exact (fun e => Sym2.ind (fun u v hu => by simpa using h (by simpa using hu)) e))
         | (have h := hMax Tz hTz (fun u v hh => hlez hh); exact SimpleGraph.edgeSet_mono h)
         | (have h := hMax Tz hTz (fun u v hh => hlez hh); exact h)
         | (have h := hMax Tz hTz (fun u v hh => hlez hh); exact le_of_eq (congrArg SimpleGraph.edgeSet h))
         | (have h := hMax Tz hTz (fun u v hh => hlez hh); exact le_of_eq (congrArg SimpleGraph.edgeSet h.symm))
         | (have h := hMax Tz hTz (fun u v hh => hlez hh); exact SimpleGraph.edgeSet_mono h.le)
         | (have h := hMax Tz hTz (fun u v hh => hlez hh); exact SimpleGraph.edgeSet_mono h.symm.le)
         | (have h := hMax Tz hTz (fun u v hh => hlez hh); exact le_of_eq h)
         | (have h := hMax Tz hTz (fun u v hh => hlez hh); exact h.le)
         | (have h := hMax Tz hTz (fun u v hh => hlez hh); exact (fun e => Sym2.ind (fun u v hu => by simpa using h u v (by simpa using hu)) e))
         | (have h := hMax Tz hTz (fun u v hh => hlez hh); exact (fun e => Sym2.ind (fun u v hu => by simpa using h (by simpa using hu)) e))
         | (have h := hMax Tz hTz (fun {u v} hh => hlez hh); exact SimpleGraph.edgeSet_mono h)
         | (have h := hMax Tz hTz (fun {u v} hh => hlez hh); exact h)
         | (have h := hMax Tz hTz (fun {u v} hh => hlez hh); exact le_of_eq (congrArg SimpleGraph.edgeSet h))
         | (have h := hMax Tz hTz (fun {u v} hh => hlez hh); exact le_of_eq (congrArg SimpleGraph.edgeSet h.symm))
         | (have h := hMax Tz hTz (fun {u v} hh => hlez hh); exact SimpleGraph.edgeSet_mono h.le)
         | (have h := hMax Tz hTz (fun {u v} hh => hlez hh); exact SimpleGraph.edgeSet_mono h.symm.le)
         | (have h := hMax Tz hTz (fun {u v} hh => hlez hh); exact le_of_eq h)
         | (have h := hMax Tz hTz (fun {u v} hh => hlez hh); exact h.le)
         | (have h := hMax Tz hTz (fun {u v} hh => hlez hh); exact (fun e => Sym2.ind (fun u v hu => by simpa using h u v (by simpa using hu)) e))
         | (have h := hMax Tz hTz (fun {u v} hh => hlez hh); exact (fun e => Sym2.ind (fun u v hu => by simpa using h (by simpa using hu)) e))
         | (have h := hMax Tz hTz (fun ⦃u v⦄ hh => hlez hh); exact SimpleGraph.edgeSet_mono h)
         | (have h := hMax Tz hTz (fun ⦃u v⦄ hh => hlez hh); exact h)
         | (have h := hMax Tz hTz (fun ⦃u v⦄ hh => hlez hh); exact le_of_eq (congrArg SimpleGraph.edgeSet h))
         | (have h := hMax Tz hTz (fun ⦃u v⦄ hh => hlez hh); exact le_of_eq (congrArg SimpleGraph.edgeSet h.symm))
         | (have h := hMax Tz hTz (fun ⦃u v⦄ hh => hlez hh); exact SimpleGraph.edgeSet_mono h.le)
         | (have h := hMax Tz hTz (fun ⦃u v⦄ hh => hlez hh); exact SimpleGraph.edgeSet_mono h.symm.le)
         | (have h := hMax Tz hTz (fun ⦃u v⦄ hh => hlez hh); exact le_of_eq h)
         | (have h := hMax Tz hTz (fun ⦃u v⦄ hh => hlez hh); exact h.le)
         | (have h := hMax Tz hTz (fun ⦃u v⦄ hh => hlez hh); exact (fun e => Sym2.ind (fun u v hu => by simpa using h u v (by simpa using hu)) e))
         | (have h := hMax Tz hTz (fun ⦃u v⦄ hh => hlez hh); exact (fun e => Sym2.ind (fun u v hu => by simpa using h (by simpa using hu)) e))
         | (by_contra hns; exact hMax Tz hTz ⟨SimpleGraph.edgeSet_mono hlez, hns⟩)
         | (by_contra hns; exact hMax Tz ⟨SimpleGraph.edgeSet_mono hlez, hns⟩ hTz)
       exact Set.ncard_le_ncard hsub (Set.toFinite _))
  have hconG : H.Connected := conn_aux H hCard hDraw (by omega)
  obtain ⟨fG, hfG3, hfGe⟩ := WilliamsonShmoys.connected_planar_drawing_euler_face_count_core H hCard hconG hDraw
  first
  | omega
  | (by_contra hd; have := ds_aux H hCard hDraw hd; omega)
  | (refine ⟨Tz, ?_⟩; and_intros <;> first | exact hlez | exact hTz | exact SimpleGraph.edgeSet_mono hlez | (intro u v hh; exact hlez hh) | omega | exact hconTz | (refine ⟨fz, ?_⟩; and_intros <;> omega) | (refine ⟨fG, ?_⟩; and_intros <;> omega))
  | (refine ⟨Hc, ?_⟩; and_intros <;> first | exact hGc | exact hHc | exact hHconn | exact SimpleGraph.edgeSet_mono hGc | (intro u v hh; exact hGc hh) | omega | exact hcc | (refine ⟨fz, ?_⟩; and_intros <;> omega))
  | (refine ⟨fG, ?_⟩; and_intros <;> omega)
  | (refine ⟨fz, ?_⟩; and_intros <;> omega)
  | (and_intros <;> first | exact hGc | exact hHc | exact hHconn | exact SimpleGraph.edgeSet_mono hGc | (intro u v hh; exact hGc hh) | omega | exact hcc | omega)
  | (refine ⟨2 * Fintype.card V - 4, ?_⟩; and_intros <;> omega)
  | (refine ⟨3 * Fintype.card V - 6, 2 * Fintype.card V - 4, ?_⟩; and_intros <;> omega)
