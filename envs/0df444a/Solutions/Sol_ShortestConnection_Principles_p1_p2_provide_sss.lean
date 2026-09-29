-- Prove2me | solution 1 for ShortestConnection.Principles.p1_p2_provide_sss
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:27:35.356652+00:00
-- url     : https://prove2.me/submissions/0707c2e0-191b-4bd5-97e4-834bc4fc67c2

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

open SimpleGraph

theorem aux_pp_reach_iso {V : Type*} {H : SimpleGraph V} {t a : V}
    (ht : ∀ x, ¬ H.Adj t x) (h : H.Reachable t a) : a = t := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons h' _ => exact absurd h' (ht _)

theorem aux_pp_reach_transfer {V : Type*} {G H : SimpleGraph V}
    (hGH : ∀ x y, G.Adj x y → H.Reachable x y) {a b : V} (h : G.Reachable a b) :
    H.Reachable a b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | cons h' _ ih => exact (hGH _ _ h').trans ih

theorem aux_pp_linkGraph_adj {V : Type*} {F : Finset (Sym2 V)} {x y : V} :
    (linkGraph F).Adj x y ↔ s(x, y) ∈ F ∧ x ≠ y := by
  unfold linkGraph
  simp [SimpleGraph.fromEdgeSet_adj]

theorem aux_pp_linkGraph_mono {V : Type*} {F F' : Finset (Sym2 V)} (h : F ⊆ F') :
    linkGraph F ≤ linkGraph F' := by
  intro x y hxy
  rw [aux_pp_linkGraph_adj] at hxy ⊢
  exact ⟨h hxy.1, hxy.2⟩

theorem aux_pp_mem_edgeSet {V : Type*} {F : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ (linkGraph F).edgeSet ↔ e ∈ F ∧ ¬ e.IsDiag := by
  unfold linkGraph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  simp

theorem aux_pp_edgeSet {V : Type*} {G : SimpleGraph V} {T : Finset (Sym2 V)}
    (hT : (T : Set (Sym2 V)) ⊆ G.edgeSet) : (linkGraph T).edgeSet = (T : Set (Sym2 V)) := by
  ext e
  rw [aux_pp_mem_edgeSet]
  constructor
  · intro he; exact he.1
  · intro he; exact ⟨he, G.not_isDiag_of_mem_edgeSet (hT he)⟩

theorem aux_pp_natcard {V : Type*} {G : SimpleGraph V} {T : Finset (Sym2 V)}
    (hT : (T : Set (Sym2 V)) ⊆ G.edgeSet) : Nat.card (linkGraph T).edgeSet = T.card := by
  rw [aux_pp_edgeSet hT]
  simp

theorem aux_pp_tree_card {V : Type*} [Fintype V] {G : SimpleGraph V} {T : Finset (Sym2 V)}
    (hT : IsSpanningSubtree G T) : T.card + 1 = Fintype.card V := by
  have := (isTree_iff_connected_and_card.mp hT.2).2
  rw [aux_pp_natcard hT.1, Nat.card_eq_fintype_card] at this
  exact this

theorem aux_pp_tree_of {V : Type*} [Fintype V] {G : SimpleGraph V} {T : Finset (Sym2 V)}
    (hsub : (T : Set (Sym2 V)) ⊆ G.edgeSet) (hc : (linkGraph T).Connected)
    (hcard : T.card + 1 = Fintype.card V) : IsSpanningSubtree G T := by
  refine ⟨hsub, isTree_iff_connected_and_card.mpr ⟨hc, ?_⟩⟩
  rw [aux_pp_natcard hsub, Nat.card_eq_fintype_card]
  exact hcard

theorem aux_pp_cross {V : Type*} [DecidableEq V] {T : Finset (Sym2 V)} (C : Set V) :
    ∀ {x y : V} (p : (linkGraph T).Walk x y), p.IsTrail → x ∈ C → y ∉ C →
    ∃ a b, a ∈ C ∧ b ∉ C ∧ s(a, b) ∈ T ∧ s(a, b) ∈ p.edges ∧
      (linkGraph (T.erase s(a, b))).Reachable x a ∧
      (linkGraph (T.erase s(a, b))).Reachable b y := by
  intro x y p
  induction p with
  | nil => intro _ hx hy; exact absurd hx hy
  | @cons x z y h q ih =>
    intro hp hx hy
    rw [Walk.isTrail_cons] at hp
    by_cases hz : z ∈ C
    · obtain ⟨a, b, ha, hb, hab, habq, h1, h2⟩ := ih hp.1 hz hy
      refine ⟨a, b, ha, hb, hab, by simp [habq], ?_, h2⟩
      refine Reachable.trans ?_ h1
      apply Adj.reachable
      rw [aux_pp_linkGraph_adj] at h ⊢
      refine ⟨Finset.mem_erase.mpr ⟨?_, h.1⟩, h.2⟩
      intro heq
      exact hp.2 (heq ▸ habq)
    · refine ⟨x, z, hx, hz, (aux_pp_linkGraph_adj.mp h).1, by simp, Reachable.refl _, ?_⟩
      refine ⟨q.transfer _ ?_⟩
      intro e he
      have he' := q.edges_subset_edgeSet he
      rw [aux_pp_mem_edgeSet] at he' ⊢
      refine ⟨Finset.mem_erase.mpr ⟨?_, he'.1⟩, he'.2⟩
      intro heq
      exact hp.2 (heq ▸ he)

theorem aux_pp_exchange {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {w : Sym2 V → ℝ} {T F : Finset (Sym2 V)} (hT : IsSSS G w T) (hFT : F ⊆ T)
    {u n : V} (hadj : G.Adj u n) (hun : ¬ (linkGraph F).Reachable u n)
    (hmin : ∀ a b, (linkGraph F).Reachable u a → ¬ (linkGraph F).Reachable u b → G.Adj a b →
      w s(u, n) ≤ w s(a, b)) :
    ∃ T', IsSSS G w T' ∧ insert s(u, n) F ⊆ T' := by
  by_cases he : s(u, n) ∈ T
  · exact ⟨T, hT, Finset.insert_subset he hFT⟩
  have hconn := hT.1.2.connected
  obtain ⟨p⟩ := hconn.preconnected u n
  obtain ⟨a, b, ha, hb, hab, _, h1, h2⟩ :=
    aux_pp_cross {x | (linkGraph F).Reachable u x} p.bypass p.bypass_isPath.isTrail
      (Reachable.refl u) hun
  have hfG : G.Adj a b := hT.1.1 hab
  have hfF : s(a, b) ∉ F := by
    intro hf
    apply hb
    exact Reachable.trans ha (Adj.reachable ((aux_pp_linkGraph_adj).mpr ⟨hf, hfG.ne⟩))
  have hwf : w s(u, n) ≤ w s(a, b) := hmin a b ha hb hfG
  have hsub : ((insert s(u, n) (T.erase s(a, b)) : Finset (Sym2 V)) : Set (Sym2 V)) ⊆
      G.edgeSet := by
    intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hadj
    · exact hT.1.1 (Finset.mem_of_mem_erase hx)
  have hne' : s(u, n) ∉ T.erase s(a, b) := fun h => he (Finset.mem_of_mem_erase h)
  have hcard : (insert s(u, n) (T.erase s(a, b))).card = T.card := by
    rw [Finset.card_insert_of_notMem hne', Finset.card_erase_of_mem hab]
    have : 0 < T.card := Finset.card_pos.mpr ⟨_, hab⟩
    omega
  have hmono : linkGraph (T.erase s(a, b)) ≤ linkGraph (insert s(u, n) (T.erase s(a, b))) :=
    aux_pp_linkGraph_mono (Finset.subset_insert _ _)
  have hadjT : ∀ x y, (linkGraph T).Adj x y →
      (linkGraph (insert s(u, n) (T.erase s(a, b)))).Reachable x y := by
    intro x y hxy
    rw [aux_pp_linkGraph_adj] at hxy
    by_cases hxf : s(x, y) = s(a, b)
    · have hab' : (linkGraph (insert s(u, n) (T.erase s(a, b)))).Reachable a b := by
        refine Reachable.trans (h1.symm.mono hmono) (Reachable.trans ?_ (h2.symm.mono hmono))
        apply Adj.reachable
        rw [aux_pp_linkGraph_adj]
        exact ⟨Finset.mem_insert_self _ _, hadj.ne⟩
      rcases Sym2.eq_iff.mp hxf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab'
      · exact hab'.symm
    · apply Adj.reachable
      rw [aux_pp_linkGraph_adj]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxf, hxy.1⟩), hxy.2⟩
  have hc : (linkGraph (insert s(u, n) (T.erase s(a, b)))).Connected := by
    have := hconn.nonempty
    exact ⟨fun x y => aux_pp_reach_transfer hadjT (hconn.preconnected x y)⟩
  have hST : IsSpanningSubtree G (insert s(u, n) (T.erase s(a, b))) :=
    aux_pp_tree_of hsub hc (hcard ▸ aux_pp_tree_card hT.1)
  have hlen : length w (insert s(u, n) (T.erase s(a, b))) ≤ length w T := by
    unfold length
    rw [Finset.sum_insert hne', ← Finset.add_sum_erase T w hab]
    linarith
  refine ⟨insert s(u, n) (T.erase s(a, b)), ⟨hST, fun F' hF' => hlen.trans (hT.2 F' hF')⟩, ?_⟩
  exact Finset.insert_subset_insert _
    (fun x hx => Finset.mem_erase.mpr ⟨fun h => hfF (h ▸ hx), hFT hx⟩)

theorem aux_pp_app_cut {V : Type*} {G : SimpleGraph V} {w : Sym2 V → ℝ} {F : Finset (Sym2 V)}
    {e : Sym2 V} (h : IsApplication G w F e) :
    ∃ u n, G.Adj u n ∧ ¬ (linkGraph F).Reachable u n ∧ e = s(u, n) ∧
      ∀ a b, (linkGraph F).Reachable u a → ¬ (linkGraph F).Reachable u b → G.Adj a b →
        w s(u, n) ≤ w s(a, b) := by
  rcases h with ⟨t, n, hiso, hadj, he, hmin⟩ | ⟨u, n, _, hr, hadj, he, hmin⟩
  · refine ⟨t, n, hadj, ?_, he, ?_⟩
    · intro hr
      exact hadj.ne (aux_pp_reach_iso hiso hr).symm
    · intro a b ha _ hab
      have := aux_pp_reach_iso hiso ha
      subst this
      exact hmin b hab
  · exact ⟨u, n, hadj, hr, he, hmin⟩

theorem aux_pp_not_mem {V : Type*} {G : SimpleGraph V} {F : Finset (Sym2 V)} {u n : V}
    (hadj : G.Adj u n) (hun : ¬ (linkGraph F).Reachable u n) : s(u, n) ∉ F := by
  intro h
  exact hun (Adj.reachable (aux_pp_linkGraph_adj.mpr ⟨h, hadj.ne⟩))

theorem aux_pp_inv {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {w : Sym2 V → ℝ} {l : List (Sym2 V)} (hl : IsConstruction G w l)
    (T0 : Finset (Sym2 V)) (hT0 : IsSSS G w T0) :
    ∀ k, k ≤ l.length →
      (l.take k).toFinset.card = k ∧ ∃ T, IsSSS G w T ∧ (l.take k).toFinset ⊆ T := by
  intro k
  induction k with
  | zero => intro _; exact ⟨by simp, T0, hT0, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨hcard, T, hT, hsub⟩ := ih (by omega)
    have hk' : k < l.length := by omega
    have happ := hl k hk'
    obtain ⟨u, n, hadj, hun, he, hmin⟩ := aux_pp_app_cut happ
    have htake : (l.take (k+1)).toFinset = insert l[k] (l.take k).toFinset := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk']
      ext x
      simp only [List.mem_toFinset, List.mem_append, Finset.mem_insert, Option.toList_some,
        List.mem_singleton]
      tauto
    rw [htake, he]
    refine ⟨?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (aux_pp_not_mem hadj hun), hcard]
    · exact aux_pp_exchange hT hsub hadj hun hmin

theorem aux_pp_exists_app {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.Connected) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (hF : F.card + 1 < Fintype.card V) :
    ∃ e, IsApplication G w F e := by
  classical
  have hnc : ¬ (linkGraph F).Connected := by
    intro hc
    have h1 := hc.card_vert_le_card_edgeSet_add_one
    have h2 : Nat.card (linkGraph F).edgeSet ≤ F.card := by
      have hsub : (linkGraph F).edgeSet ⊆ (F : Set (Sym2 V)) := by
        intro e he
        exact (aux_pp_mem_edgeSet.mp he).1
      calc Nat.card (linkGraph F).edgeSet ≤ Nat.card (F : Set (Sym2 V)) :=
            Nat.card_mono (Finset.finite_toSet F) hsub
        _ = F.card := by simp
    rw [Nat.card_eq_fintype_card] at h1
    omega
  have hne := hG.nonempty
  obtain ⟨u0, v0, huv⟩ : ∃ u0 v0, ¬ (linkGraph F).Reachable u0 v0 := by
    by_contra hcon
    push Not at hcon
    exact hnc ⟨hcon⟩
  obtain ⟨p⟩ := hG.preconnected u0 v0
  obtain ⟨d, _, hd1, hd2⟩ :=
    p.exists_boundary_dart {x | (linkGraph F).Reachable u0 x} (Reachable.refl _) huv
  let S := (Finset.univ : Finset (V × V)).filter (fun q => (linkGraph F).Reachable u0 q.1 ∧
    ¬ (linkGraph F).Reachable u0 q.2 ∧ G.Adj q.1 q.2)
  have hS : S.Nonempty := ⟨(d.fst, d.snd), by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hd1, hd2, d.adj⟩⟩
  obtain ⟨⟨a0, b0⟩, hmem, hmin⟩ := S.exists_min_image (fun q => w s(q.1, q.2)) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨ha0, hb0, hab0⟩ := hmem
  by_cases hlink : ∃ x, (linkGraph F).Adj a0 x
  · refine ⟨s(a0, b0), Or.inr ⟨a0, b0, hlink, ?_, hab0, rfl, ?_⟩⟩
    · intro h; exact hb0 (ha0.trans h)
    · intro u' n' hu' hn' hadj'
      apply hmin (u', n')
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ha0.trans hu', fun h => hn' (ha0.symm.trans h), hadj'⟩
  · push Not at hlink
    refine ⟨s(a0, b0), Or.inl ⟨a0, b0, hlink, hab0, rfl, ?_⟩⟩
    intro m hm
    apply hmin (a0, m)
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨ha0, ?_, hm⟩
    intro h
    have := aux_pp_reach_iso hlink (ha0.symm.trans h)
    exact hm.ne this.symm

theorem aux_pp_exists_list {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.Connected) (w : Sym2 V → ℝ) :
    ∀ k, k ≤ Fintype.card V - 1 → ∃ l : List (Sym2 V), IsConstruction G w l ∧ l.length = k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨[], fun i h => absurd h (by simp), rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨l, hl, hlen⟩ := ih (by omega)
    have hcard : l.toFinset.card + 1 < Fintype.card V := by
      have := List.toFinset_card_le l
      omega
    obtain ⟨e, he⟩ := aux_pp_exists_app hG w l.toFinset hcard
    refine ⟨l ++ [e], ?_, by simp [hlen]⟩
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hik : i < l.length
    · have h1 : (l ++ [e]).take i = l.take i := List.take_append_of_le_length hik.le
      have h2 : (l ++ [e])[i] = l[i] := List.getElem_append_left hik
      rw [h1, h2]; exact hl i hik
    · have hi' : i = l.length := by omega
      subst hi'
      have h1 : (l ++ [e]).take l.length = l := by simp
      have h2 : (l ++ [e])[l.length] = e := by simp
      rw [h1, h2]; exact he

theorem aux_pp_exists_sss {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.Connected) (w : Sym2 V → ℝ) : ∃ T, IsSSS G w T := by
  classical
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  have hST : IsSpanningSubtree G T.edgeFinset := by
    refine ⟨?_, ?_⟩
    · intro e he
      rw [SimpleGraph.coe_edgeFinset] at he
      exact edgeSet_mono hTG he
    · unfold linkGraph
      rw [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
      exact hT
  let S := (Finset.univ : Finset (Finset (Sym2 V))).filter (IsSpanningSubtree G)
  obtain ⟨T1, hT1, hmin⟩ := S.exists_min_image (length w) ⟨_, by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hST⟩
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hT1
  exact ⟨T1, hT1, fun F' hF' => hmin F' (by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hF')⟩

end ShortestConnection.Principles

open ShortestConnection.Principles

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) :
    (∃ l : List (Sym2 V), IsCompleteConstruction G w l) ∧
      ∀ l : List (Sym2 V), IsCompleteConstruction G w l → IsSSS G w l.toFinset := by
  refine ⟨?_, ?_⟩
  · obtain ⟨l, hl, hlen⟩ := aux_pp_exists_list hG w (Fintype.card V - 1) le_rfl
    exact ⟨l, hl, hlen⟩
  · rintro l ⟨hl, hlen⟩
    obtain ⟨T0, hT0⟩ := aux_pp_exists_sss hG w
    obtain ⟨hcard, T, hT, hsub⟩ := aux_pp_inv hl T0 hT0 l.length le_rfl
    rw [List.take_length] at hcard hsub
    have hTc := aux_pp_tree_card hT.1
    have hne := hG.nonempty
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    have : l.toFinset = T := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [this]; exact hT
