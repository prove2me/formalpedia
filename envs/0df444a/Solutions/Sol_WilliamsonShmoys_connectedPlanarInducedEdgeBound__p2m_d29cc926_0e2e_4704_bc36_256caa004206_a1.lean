-- Prove2me | solution 1 for WilliamsonShmoys.connectedPlanarInducedEdgeBound__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T08:53:28.373515+00:00
-- url     : https://prove2.me/submissions/93d27dbc-1a01-49f6-9626-d45aadef75f0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_connected
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem planarDrawingOn_induce_local
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (s : Finset V) :
    HasPlanarDrawingOn (L.induce (↑s : Set V)) := by
  classical
  rcases hL with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨(fun u : (↑s : Set V) => p u.1),
    (fun u v t => arc u.1 v.1 t), ?_, ?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    exact hp (by simpa using huv)
  · intro u v huv hadj
    have huv' : (u : V) < (v : V) := huv
    change L.Adj (u : V) (v : V) at hadj
    obtain ⟨hcont, hinj, hstart, hfinish, hnov⟩ := hedge u.1 v.1 huv' hadj
    refine ⟨hcont, hinj, hstart, hfinish, ?_⟩
    intro t ht w heq
    apply hnov t ht w.1
    exact heq
  · intro u v x y huv hxy hadj hadj' hne t ht w hw heq
    have huv' : (u : V) < (v : V) := huv
    have hxy' : (x : V) < (y : V) := hxy
    change L.Adj (u : V) (v : V) at hadj
    change L.Adj (x : V) (y : V) at hadj'
    have hne' : ((u : V), (v : V)) ≠ ((x : V), (y : V)) := by
      intro he
      apply hne
      exact Prod.ext
        (Subtype.ext (congrArg Prod.fst he))
        (Subtype.ext (congrArg Prod.snd he))
    exact hcross u.1 v.1 x.1 y.1 huv' hxy' hadj hadj' hne' t ht w hw heq

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (s : Finset V) (hconn : (L.induce (↑s : Set V)).Connected) :
    (letI : DecidableRel L.Adj := dL
     (L.induce (↑s : Set V)).edgeFinset.card) + 3 ≤ 3 * s.card := by
  classical
  letI : DecidableRel L.Adj := dL
  let G := L.induce (↑s : Set V)
  have hdraw : HasPlanarDrawingOn G := planarDrawingOn_induce_local L hL s
  have hcard : Fintype.card (↑s : Set V) = s.card := by simp
  by_cases hbig : 3 ≤ Fintype.card (↑s : Set V)
  · have hbound :=
      WilliamsonShmoys.planar_drawing_edge_bound_connected G hdraw hconn hbig
    have hedgecount : G.edgeFinset.card = G.edgeSet.ncard := by
      calc
        G.edgeFinset.card = Fintype.card G.edgeSet := G.edgeFinset_card
        _ = G.edgeSet.ncard := by
          rw [Set.ncard_eq_toFinset_card]
          simp [SimpleGraph.edgeFinset]
    change G.edgeFinset.card + 3 ≤ 3 * s.card
    rw [← hcard, hedgecount]
    omega
  · have hs : s.Nonempty := by
      rcases hconn.nonempty with ⟨x⟩
      exact ⟨x.1, x.2⟩
    have hpos : 0 < Fintype.card (↑s : Set V) := by
      rw [hcard]
      exact Finset.card_pos.mpr hs
    have hsmall : Fintype.card (↑s : Set V) = 1 ∨
        Fintype.card (↑s : Set V) = 2 := by omega
    have hchoose : G.edgeFinset.card ≤ (Fintype.card (↑s : Set V)).choose 2 :=
      G.card_edgeFinset_le_card_choose_two
    change G.edgeFinset.card + 3 ≤ 3 * s.card
    rcases hsmall with hone | htwo
    · have hle : G.edgeFinset.card ≤ 0 := by
        calc
          G.edgeFinset.card ≤ (Fintype.card (↑s : Set V)).choose 2 := hchoose
          _ = 0 := by rw [hone]; norm_num
      omega
    · have hle : G.edgeFinset.card ≤ 1 := by
        calc
          G.edgeFinset.card ≤ (Fintype.card (↑s : Set V)).choose 2 := hchoose
          _ = 1 := by rw [htwo]; norm_num
      omega
