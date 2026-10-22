-- Prove2me | solution 1 for SnarkGen.EdgeInsertion.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T02:39:01.435371+00:00
-- url     : https://prove2.me/submissions/57f208fc-cc74-4728-9ce2-603b28608657

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_Colourable
import Definitions.Def_SnarkGen_EdgeInsertion_twoColourFactor
import Definitions.Def_SnarkGen_EdgeInsertion_insertEdge

set_option autoImplicit false

namespace FE6EC70A

open SimpleGraph

theorem mem_of_closed {V : Type*} {G : SimpleGraph V} (S : Set V)
    (hS : ∀ u v, u ∈ S → G.Adj u v → v ∈ S) {a b : V} (ha : a ∈ S) (h : G.Reachable a b) :
    b ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons hadj p ih => exact ih (hS _ _ ha hadj)

theorem not_reach {V : Type*} [Fintype V] [DecidableEq V] {F H : SimpleGraph V}
    [DecidableRel F.Adj] (hF : F.IsCycles) (hHF : H ≤ F) {u v x y : V}
    (hH : ∀ p q, H.Adj p q → s(p, q) ≠ s(u, v) ∧ s(p, q) ≠ s(x, y))
    (huv : F.Adj u v) (hxy : F.Adj x y) (hne : s(u, v) ≠ s(x, y)) (hux : F.Reachable u x) :
    ¬ H.Reachable u v := by
  rintro ⟨p⟩
  set P : F.Walk u v := p.bypass.mapLe hHF with hP
  have hPpath : P.IsPath := (Walk.bypass_isPath p).mapLe hHF
  have hPe : ∀ e ∈ P.edges, e ≠ s(u, v) ∧ e ≠ s(x, y) := by
    intro e he
    rw [hP, Walk.edges_mapLe_eq_edges] at he
    have he2 : e ∈ H.edgeSet := p.edges_subset_edgeSet (p.edges_bypass_subset_edges he)
    induction e using Sym2.ind with
    | h q r => exact hH q r he2
  let W : F.Walk v v := Walk.cons huv.symm P
  have hW : W.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨hPpath, fun h => (hPe _ h).1 (Sym2.eq_swap)⟩
  have hclosed : ∀ p q, p ∈ W.toSubgraph.verts → F.Adj p q → q ∈ W.toSubgraph.verts := by
    intro p q hp hpq
    exact ((hW.adj_toSubgraph_iff_of_isCycles hF hp q).2 hpq).snd_mem
  have hu : u ∈ W.toSubgraph.verts := by
    rw [Walk.mem_verts_toSubgraph]; simp [W]
  have hx : x ∈ W.toSubgraph.verts := mem_of_closed _ hclosed hu hux
  have hadj := (hW.adj_toSubgraph_iff_of_isCycles hF hx y).2 hxy
  have hmem : s(x, y) ∈ W.edges := (Walk.mem_edges_toSubgraph W).1 hadj
  simp only [W, Walk.edges_cons, List.mem_cons] at hmem
  rcases hmem with h | h
  · exact hne (h.trans Sym2.eq_swap).symm
  · exact (hPe _ h).2 rfl

def Hg {V : Type*} (G : SimpleGraph V) (col : Sym2 V → Fin 3) (j : Fin 3) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ col s(a, b) ≠ j
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

theorem Hg_isCycles {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcubic : G.IsRegularOfDegree 3) (col : Sym2 V → Fin 3)
    (hcol : ∀ v w w', G.Adj v w → G.Adj v w' → w ≠ w' → col s(v, w) ≠ col s(v, w'))
    (j : Fin 3) : (Hg G col j).IsCycles := by
  classical
  intro v _
  have hN : (G.neighborFinset v).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hcubic v
  have hinj : Set.InjOn (fun w => col s(v, w)) (G.neighborFinset v : Set V) := by
    intro w hw w' hw' h
    by_contra hne
    exact hcol v w w' (by simpa using hw) (by simpa using hw') hne h
  have himg : (G.neighborFinset v).image (fun w => col s(v, w)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, hN]; simp
  have hset : (Hg G col j).neighborSet v =
      ↑((G.neighborFinset v).filter (fun w => col s(v, w) ≠ j)) := by
    ext w
    simp [Hg]
  rw [hset, Set.ncard_coe_finset]
  have : ((G.neighborFinset v).filter (fun w => col s(v, w) ≠ j)).image (fun w => col s(v, w))
      = Finset.univ.erase j := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨w, ⟨_, h⟩, rfl⟩; exact h
    · intro hx
      have : x ∈ (G.neighborFinset v).image (fun w => col s(v, w)) := by rw [himg]; simp
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 this
      exact ⟨w, ⟨hw, hx⟩, rfl⟩
  rw [← Finset.card_image_of_injOn (f := fun w => col s(v, w)), this]
  · simp
  · exact hinj.mono (by intro w hw; exact Finset.mem_filter.1 hw |>.1)

/-- The colouring of the new graph, as a function of ordered vertex pairs. -/
def fcol {V : Type*} (R : V → Prop) [DecidablePred R] (col : Sym2 V → Fin 3) (i j κ : Fin 3)
    (e e' : Sym2 V) : V ⊕ Fin 2 → V ⊕ Fin 2 → Fin 3
  | .inl u, .inl v => if R u ∨ R v then Equiv.swap i j (col s(u, v)) else col s(u, v)
  | .inl u, .inr k => if R u then Equiv.swap i j (col (![e, e'] k)) else col (![e, e'] k)
  | .inr k, .inl u => if R u then Equiv.swap i j (col (![e, e'] k)) else col (![e, e'] k)
  | .inr _, .inr _ => κ

theorem fcol_symm {V : Type*} (R : V → Prop) [DecidablePred R] (col : Sym2 V → Fin 3)
    (i j κ : Fin 3) (e e' : Sym2 V) (x y : V ⊕ Fin 2) :
    fcol R col i j κ e e' x y = fcol R col i j κ e e' y x := by
  rcases x with u | k <;> rcases y with v | l <;> simp [fcol, or_comm, Sym2.eq_swap]

theorem fin3_aux : ∀ t i j κ : Fin 3, i ≠ j → κ ≠ i → κ ≠ j → (t ≠ κ ↔ t = i ∨ t = j) := by
  decide

theorem fin3_third : ∀ i j : Fin 3, ∃ κ : Fin 3, κ ≠ i ∧ κ ≠ j := by decide

end FE6EC70A

open SnarkGen.EdgeInsertion in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3) (C : G.lineGraph.Coloring (Fin 3))
    (i j : Fin 3) (hij : i ≠ j) (a b c d : V)
    (hab : (twoColourFactor C i j).Adj a b) (hcd : (twoColourFactor C i j).Adj c d)
    (hne : s(a, b) ≠ s(c, d)) (hsame : (twoColourFactor C i j).Reachable a c) :
    Colourable (insertEdge G s(a, b) s(c, d)) := by
  classical
  set F := twoColourFactor C i j with hFdef
  let col : Sym2 V → Fin 3 := fun e => if h : e ∈ G.edgeSet then C ⟨e, h⟩ else 0
  have hcolv : ∀ v w w', G.Adj v w → G.Adj v w' → w ≠ w' → col s(v, w) ≠ col s(v, w') := by
    intro v w w' h1 h2 hne
    have e1 : s(v, w) ∈ G.edgeSet := h1
    have e2 : s(v, w') ∈ G.edgeSet := h2
    simp only [col, dif_pos e1, dif_pos e2]
    apply C.valid
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨?_, v, by simp, by simp⟩
    intro h
    apply hne
    have := congrArg Subtype.val h
    exact Sym2.congr_right.1 this
  obtain ⟨κ, hκi, hκj⟩ := FE6EC70A.fin3_third i j
  have hFadj : ∀ u v, F.Adj u v ↔ G.Adj u v ∧ (col s(u, v) = i ∨ col s(u, v) = j) := by
    intro u v
    simp only [F, twoColourFactor, SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq, col]
    constructor
    · rintro ⟨⟨h, hc⟩, -⟩
      exact ⟨h, by rw [dif_pos h]; exact hc⟩
    · rintro ⟨h, hc⟩
      rw [dif_pos (G.mem_edgeSet.2 h)] at hc
      exact ⟨⟨G.mem_edgeSet.2 h, hc⟩, G.ne_of_adj h⟩
  have hFeq : F = FE6EC70A.Hg G col κ := by
    ext u v
    rw [hFadj]
    simp only [FE6EC70A.Hg]
    rw [FE6EC70A.fin3_aux (col s(u, v)) i j κ hij hκi hκj]
  have hFc : F.IsCycles := hFeq ▸ FE6EC70A.Hg_isCycles G hG col hcolv κ
  -- the graph H: the two-colour factor minus the two edges
  set H := F.deleteEdges {s(a, b), s(c, d)} with hHdef
  have hHadj : ∀ p q, H.Adj p q ↔ F.Adj p q ∧ s(p, q) ≠ s(a, b) ∧ s(p, q) ≠ s(c, d) := by
    intro p q
    simp [H, SimpleGraph.deleteEdges_adj]
  have hHF : H ≤ F := SimpleGraph.deleteEdges_le _
  have hF1 : ¬ H.Reachable a b :=
    FE6EC70A.not_reach hFc hHF (fun p q h => ((hHadj p q).1 h).2) hab hcd hne hsame
  have hF2 : ¬ H.Reachable c d :=
    FE6EC70A.not_reach hFc hHF (fun p q h => ⟨((hHadj p q).1 h).2.2, ((hHadj p q).1 h).2.1⟩) hcd hab
      (Ne.symm hne) hsame.symm
  have hF3 : H.Reachable a c ∨ H.Reachable a d := by
    by_contra hcon
    push_neg at hcon
    have hr := hFc.reachable_deleteEdges hab
    apply hF1
    refine FE6EC70A.mem_of_closed (G := F.deleteEdges {s(a, b)}) {v | H.Reachable a v} ?_
      (SimpleGraph.Reachable.refl a) hr
    intro u w hu huw
    rw [SimpleGraph.deleteEdges_adj] at huw
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hu huw ⊢
    by_cases hcd' : s(u, w) = s(c, d)
    · exfalso
      have : u ∈ s(c, d) := hcd' ▸ Sym2.mem_mk_left u w
      rcases Sym2.mem_iff.1 this with rfl | rfl
      · exact hcon.1 hu
      · exact hcon.2 hu
    · exact hu.trans ((hHadj u w).2 ⟨huw.1, huw.2, hcd'⟩).reachable
  have hxor : H.Reachable a c ↔ ¬ H.Reachable a d := by
    constructor
    · intro hc hd
      exact hF2 (hc.symm.trans hd)
    · intro hd
      rcases hF3 with h | h
      · exact h
      · exact absurd h hd
  -- the colouring of the new graph
  set R : V → Prop := fun v => H.Reachable a v with hRdef
  let E : Fin 2 → Sym2 V := ![s(a, b), s(c, d)]
  let f := FE6EC70A.fcol R col i j κ s(a, b) s(c, d)
  let g : Sym2 (V ⊕ Fin 2) → Fin 3 :=
    Sym2.lift ⟨f, fun x y => FE6EC70A.fcol_symm R col i j κ _ _ x y⟩
  let σ : V → Fin 3 → Fin 3 := fun u t => if R u then Equiv.swap i j t else t
  have hRa : R a := SimpleGraph.Reachable.refl a
  have habG := ((hFadj a b).1 hab)
  have hcdG := ((hFadj c d).1 hcd)
  have hEG : ∀ k, E k ∈ G.edgeSet := by
    intro k; fin_cases k
    · exact habG.1
    · exact hcdG.1
  have hEij : ∀ k, col (E k) = i ∨ col (E k) = j := by
    intro k; fin_cases k
    · exact habG.2
    · exact hcdG.2
  have hsw : ∀ t, (t = i ∨ t = j) →
      Equiv.swap i j t ≠ t ∧ (Equiv.swap i j t = i ∨ Equiv.swap i j t = j) := by
    intro t ht
    rcases ht with rfl | rfl
    · simp [Equiv.swap_apply_left, hij, Ne.symm hij]
    · simp [Equiv.swap_apply_right, hij, Ne.symm hij]
  have hσij : ∀ u t, (t = i ∨ t = j) → (σ u t = i ∨ σ u t = j) := by
    intro u t ht
    by_cases hRu : R u
    · simp only [σ, hRu, if_true]; exact (hsw t ht).2
    · simp only [σ, hRu, if_false]; exact ht
  have hσinj : ∀ u t t', σ u t = σ u t' → t = t' := by
    intro u t t' h
    by_cases hRu : R u
    · simp only [σ, hRu, if_true] at h; exact (Equiv.swap i j).injective h
    · simpa [σ, hRu] using h
  have hE3 : ∀ u E1 E2, E1 ∈ G.edgeSet → E2 ∈ G.edgeSet → u ∈ E1 → u ∈ E2 → E1 ≠ E2 →
      col E1 ≠ col E2 := by
    intro u E1 E2 h1 h2 hu1 hu2 h12
    obtain ⟨o, rfl⟩ := Sym2.mem_iff_exists.1 hu1
    obtain ⟨o', rfl⟩ := Sym2.mem_iff_exists.1 hu2
    exact hcolv u o o' (G.mem_edgeSet.1 h1) (G.mem_edgeSet.1 h2) (fun h => h12 (h ▸ rfl))
  have hT : ∀ u v, G.Adj u v → s(u, v) ≠ s(a, b) → s(u, v) ≠ s(c, d) →
      f (Sum.inl u) (Sum.inl v) = σ u (col s(u, v)) := by
    intro u v huv h1 h2
    show (if R u ∨ R v then Equiv.swap i j (col s(u, v)) else col s(u, v)) = σ u (col s(u, v))
    by_cases hc : col s(u, v) = i ∨ col s(u, v) = j
    · have hH : H.Adj u v := (hHadj u v).2 ⟨(hFadj u v).2 ⟨huv, hc⟩, h1, h2⟩
      have hiff : R u ↔ R v :=
        ⟨fun h => h.trans hH.reachable, fun h => h.trans hH.symm.reachable⟩
      by_cases hRu : R u
      · simp [σ, hRu]
      · have hRv : ¬ R v := fun h => hRu (hiff.2 h)
        simp [σ, hRu, hRv]
    · push_neg at hc
      have hfix : Equiv.swap i j (col s(u, v)) = col s(u, v) :=
        Equiv.swap_apply_of_ne_of_ne hc.1 hc.2
      simp only [σ, hfix, ite_self]
  have hdiff : ∀ k u v, u ∈ E k → v ∈ E k → u ≠ v → (R u ↔ ¬ R v) := by
    intro k u v hu hv huv
    fin_cases k
    · simp only [E, Fin.zero_eta, Matrix.cons_val_zero, Sym2.mem_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl huv
      · exact ⟨fun _ => hF1, fun _ => hRa⟩
      · exact ⟨fun h => absurd h hF1, fun h => absurd hRa h⟩
      · exact absurd rfl huv
    · simp only [E, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Sym2.mem_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl huv
      · exact hxor
      · constructor
        · intro hd hc; exact (hxor.1 hc) hd
        · intro hc; by_contra hd; exact hc (hxor.2 hd)
      · exact absurd rfl huv
  have hvert : ∀ w p q, (insertEdge G s(a, b) s(c, d)).Adj w p →
      (insertEdge G s(a, b) s(c, d)).Adj w q → p ≠ q → f w p ≠ f w q := by
    intro w p q h1 h2 hpq
    rcases w with u | k
    · let ε : V ⊕ Fin 2 → Sym2 V := fun p => Sum.elim (fun v => s(u, v)) E p
      have hA : ∀ p, (insertEdge G s(a, b) s(c, d)).Adj (Sum.inl u) p →
          ε p ∈ G.edgeSet ∧ u ∈ ε p ∧ f (Sum.inl u) p = σ u (col (ε p)) := by
        intro p hp
        rcases p with v | k
        · simp only [insertEdge, insertEdgeAdj] at hp
          exact ⟨hp.1, Sym2.mem_mk_left u v, hT u v hp.1 hp.2.1 hp.2.2⟩
        · simp only [insertEdge, insertEdgeAdj] at hp
          exact ⟨hEG k, hp, rfl⟩
      have hB : ε p ≠ ε q := by
        rcases p with v | k <;> rcases q with v' | l
        · intro h
          apply hpq
          simp only [ε, Sum.elim_inl] at h
          rw [Sym2.congr_right.1 h]
        · simp only [insertEdge, insertEdgeAdj] at h1 h2
          simp only [ε, Sum.elim_inl, Sum.elim_inr]
          fin_cases l
          · exact h1.2.1
          · exact h1.2.2
        · simp only [insertEdge, insertEdgeAdj] at h1 h2
          simp only [ε, Sum.elim_inl, Sum.elim_inr]
          fin_cases k
          · exact Ne.symm h2.2.1
          · exact Ne.symm h2.2.2
        · simp only [ε, Sum.elim_inr]
          have hkl : k ≠ l := fun h => hpq (h ▸ rfl)
          fin_cases k <;> fin_cases l
          · exact absurd rfl hkl
          · exact hne
          · exact Ne.symm hne
          · exact absurd rfl hkl
      obtain ⟨hp1, hp2, hp3⟩ := hA p h1
      obtain ⟨hq1, hq2, hq3⟩ := hA q h2
      rw [hp3, hq3]
      intro h
      exact hE3 u _ _ hp1 hq1 hp2 hq2 hB (hσinj u _ _ h)
    · rcases p with u | l <;> rcases q with v | l'
      · simp only [insertEdge, insertEdgeAdj] at h1 h2
        have huv : u ≠ v := fun h => hpq (h ▸ rfl)
        show σ u (col (E k)) ≠ σ v (col (E k))
        have hd := hdiff k u v h1 h2 huv
        have ht := hsw _ (hEij k)
        by_cases hRu : R u
        · have hRv : ¬ R v := hd.1 hRu
          simp only [σ, hRu, hRv, if_true, if_false]
          exact ht.1
        · have hRv : R v := by by_contra h; exact hRu (hd.2 h)
          simp only [σ, hRu, hRv, if_true, if_false]
          exact Ne.symm ht.1
      · show σ u (col (E k)) ≠ κ
        rcases hσij u _ (hEij k) with h | h <;> rw [h]
        · exact Ne.symm hκi
        · exact Ne.symm hκj
      · show κ ≠ σ v (col (E k))
        rcases hσij v _ (hEij k) with h | h <;> rw [h]
        · exact hκi
        · exact hκj
      · simp only [insertEdge, insertEdgeAdj] at h1 h2
        exfalso
        apply hpq
        congr 1
        omega
  show Nonempty ((insertEdge G s(a, b) s(c, d)).lineGraph.Coloring (Fin 3))
  refine ⟨SimpleGraph.Coloring.mk (fun e => g e.1) ?_⟩
  intro e1 e2 hadj
  obtain ⟨e1, he1⟩ := e1
  obtain ⟨e2, he2⟩ := e2
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  obtain ⟨hne12, w, hw1, hw2⟩ := hadj
  obtain ⟨p, rfl⟩ := Sym2.mem_iff_exists.1 hw1
  obtain ⟨q, rfl⟩ := Sym2.mem_iff_exists.1 hw2
  have hpq : p ≠ q := by rintro rfl; exact hne12 rfl
  simp only [g, Sym2.lift_mk]
  exact hvert w p q he1 he2 hpq
