-- Prove2me | solution 1 for TwinWidthI.MinorFree.indep_mul_clique_ge
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-03T23:41:15.397093+00:00
-- url     : https://prove2.me/submissions/cddf37bf-4bee-4f8d-8d1f-317fcc8467cf

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting
import Definitions.Def_TwinWidthI_MinorFree_Setting

universe u

namespace AlphaOmegaAux

namespace ChordAux

open SimpleGraph

/-- first hit of a set along a walk -/
theorem first_hit {β : Type*} {T : SimpleGraph β} (S : Set β) :
    ∀ {x y : β} (q : T.Walk x y), y ∈ S →
      ∃ m ∈ S, ∃ (q' : T.Walk x m) (q'' : T.Walk m y), q = q'.append q'' ∧
        ∀ z ∈ q'.support, z ∈ S → z = m := by
  intro x y q
  induction q with
  | nil =>
    intro hy
    exact ⟨_, hy, Walk.nil, Walk.nil, rfl, by simp⟩
  | @cons a b c h q ih =>
    intro hy
    by_cases ha : a ∈ S
    · exact ⟨a, ha, Walk.nil, Walk.cons h q, rfl, by simp⟩
    · obtain ⟨m, hm, q', q'', hq, hz⟩ := ih hy
      refine ⟨m, hm, Walk.cons h q', q'', by simp [hq], ?_⟩
      intro z hz1 hz2
      rw [Walk.support_cons, List.mem_cons] at hz1
      rcases hz1 with rfl | hz1
      · exact absurd hz2 ha
      · exact hz z hz1 hz2

theorem path_eq {β : Type*} {T : SimpleGraph β} (hT : T.IsTree) {u v : β} {p p' : T.Walk u v}
    (hp : p.IsPath) (hp' : p'.IsPath) : p = p' := by
  have := hT.isAcyclic.subsingleton_path u v
  have h1 : (⟨p, hp⟩ : T.Path u v) = ⟨p', hp'⟩ := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

/-- a subtree containing two vertices contains the path between them -/
theorem path_support_subset {β : Type*} {T : SimpleGraph β} (hT : T.IsTree) {t : Set β}
    (ht : (T.induce t).Connected) {a b : β} (ha : a ∈ t) (hb : b ∈ t) (p : T.Walk a b)
    (hp : p.IsPath) : ∀ z ∈ p.support, z ∈ t := by
  classical
  obtain ⟨w⟩ := ht.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  let w' : T.Walk a b := w.map (SimpleGraph.Embedding.induce t).toHom
  have hw' : ∀ z ∈ w'.support, z ∈ t := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce t).toHom).support := hz
    rw [Walk.support_map, List.mem_map] at hz'
    obtain ⟨y, _, rfl⟩ := hz'
    exact y.2
  have h2 : w'.bypass = p := path_eq hT w'.bypass_isPath hp
  intro z hz
  rw [← h2] at hz
  exact hw' z (w'.support_bypass_subset_support hz)

theorem median {β : Type*} {T : SimpleGraph β} (hT : T.IsTree) (a₁ a₂ a₃ : β) :
    ∃ m : β, (∀ p : T.Walk a₁ a₂, p.IsPath → m ∈ p.support) ∧
      (∀ p : T.Walk a₁ a₃, p.IsPath → m ∈ p.support) ∧
      (∀ p : T.Walk a₂ a₃, p.IsPath → m ∈ p.support) := by
  classical
  obtain ⟨p, hp⟩ := hT.connected.preconnected a₁ a₂ |>.exists_isPath
  obtain ⟨q, hq⟩ := hT.connected.preconnected a₃ a₁ |>.exists_isPath
  obtain ⟨m, hmS, q', q'', hqq, hz⟩ := first_hit {z | z ∈ p.support} q (p.start_mem_support)
  have hmp : m ∈ p.support := hmS
  have hq' : q'.IsPath := by
    have : (q'.append q'').IsPath := hqq ▸ hq
    exact this.of_append_left
  have hp2 : (p.dropUntil m hmp).IsPath := hp.dropUntil hmp
  have hr : (q'.append (p.dropUntil m hmp)).IsPath := by
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
    have h3 := hp2.support_nodup
    rw [← Walk.cons_tail_support, List.nodup_cons] at h3
    refine ⟨hq'.support_nodup, h3.2, ?_⟩
    intro z hz1 z' hz2 hzz
    subst hzz
    have hz3 : z ∈ p.support :=
      p.support_dropUntil_subset_support hmp (List.mem_of_mem_tail hz2)
    have := hz z hz1 hz3
    rw [this] at hz2
    exact h3.1 hz2
  have hmq' : m ∈ q'.support := q'.end_mem_support
  refine ⟨m, ?_, ?_, ?_⟩
  · intro p' hp'
    rw [← path_eq hT hp hp']
    exact hmp
  · intro p' hp'
    have := path_eq hT hp'.reverse hq
    have h4 : m ∈ q.support := by
      rw [hqq, Walk.support_append]
      exact List.mem_append_left _ hmq'
    have h5 : m ∈ p'.reverse.support := by rw [this]; exact h4
    simpa using h5
  · intro p' hp'
    have := path_eq hT hp'.reverse hr
    have h5 : m ∈ p'.reverse.support := by
      rw [this, Walk.support_append]
      exact List.mem_append_left _ hmq'
    simpa using h5
end ChordAux

namespace ChordAux

theorem three_point {β : Type u} (T : SimpleGraph β) (hT : T.IsTree)
    {ι : Type*} (t : ι → Set β) (ht : ∀ i, (T.induce (t i)).Connected) (a₁ a₂ a₃ : β)
    (h : ∀ i, (a₁ ∈ t i ∧ a₂ ∈ t i) ∨ (a₁ ∈ t i ∧ a₃ ∈ t i) ∨ (a₂ ∈ t i ∧ a₃ ∈ t i)) :
    (⋂ i, t i).Nonempty := by
  obtain ⟨m, h12, h13, h23⟩ := ChordAux.median hT a₁ a₂ a₃
  obtain ⟨p12, hp12⟩ := hT.connected.preconnected a₁ a₂ |>.exists_isPath
  obtain ⟨p13, hp13⟩ := hT.connected.preconnected a₁ a₃ |>.exists_isPath
  obtain ⟨p23, hp23⟩ := hT.connected.preconnected a₂ a₃ |>.exists_isPath
  refine ⟨m, Set.mem_iInter.2 fun i => ?_⟩
  rcases h i with ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩
  · exact ChordAux.path_support_subset hT (ht i) x y p12 hp12 m (h12 p12 hp12)
  · exact ChordAux.path_support_subset hT (ht i) x y p13 hp13 m (h13 p13 hp13)
  · exact ChordAux.path_support_subset hT (ht i) x y p23 hp23 m (h23 p23 hp23)

end ChordAux

namespace ChordAux

open SimpleGraph

theorem key {V : Type u} {β : Type u} {G : SimpleGraph V} {T : SimpleGraph β} {F : V → Set β}
    (hF : GavrilSubtree.Chordal.IsSubtreeRep G T F) :
    ∀ n : ℕ, ∀ {a b : V} (q : G.Walk a b), q.length = n + 2 → q.IsPath →
    ∀ W : Set β, (T.induce W).Connected → (W ∩ F a).Nonempty → (W ∩ F b).Nonempty →
    (∀ x ∈ q.support, x ≠ a → x ≠ b → W ∩ F x = ∅) →
    (∀ x ∈ q.support, ∀ y ∈ q.support, (F x ∩ F y).Nonempty → x = y ∨ s(x, y) ∈ q.edges) →
    False := by
  intro n
  induction n with
  | zero =>
    intro a b q hlen hq W hW ha hb hint hind
    cases q with
    | nil => simp at hlen
    | @cons _ a' _ h q' =>
      cases q' with
      | nil => simp at hlen
      | @cons _ a'' _ h2 q'' =>
        have hq0 : q''.length = 0 := by simpa using hlen
        have hba : a'' = b := q''.eq_of_length_eq_zero hq0
        subst hba
        cases q'' with
        | cons _ _ => simp at hq0
        | nil =>
          rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff] at hq
          simp at hq
          obtain ⟨hq1, hq2, hq3⟩ := hq
          have haa' : a ≠ a' := h.ne
          have ha'a'' : a' ≠ a'' := h2.ne
          have haa'' : a ≠ a'' := hq3
          have e1 : (F a ∩ F a').Nonempty := (hF.2.2 a a' haa').1 h
          have e2 : (F a' ∩ F a'').Nonempty := (hF.2.2 a' a'' ha'a'').1 h2
          have e3 : F a ∩ F a'' = ∅ := by
            by_contra hne
            obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
            rcases hind a (by simp) a'' (by simp) ⟨y, hy⟩ with e | e
            · exact haa'' e
            · simp at e
              grind
          have e4 : W ∩ F a' = ∅ := hint a' (by simp) haa'.symm ha'a''
          obtain ⟨x1, hx1⟩ := e1
          obtain ⟨x2, hx2⟩ := e2
          obtain ⟨x3, hx3⟩ := hb
          have hU : (T.induce (W ∪ F a)).Connected :=
            SimpleGraph.induce_union_connected hW.preconnected (hF.2.1 a).preconnected
              (by obtain ⟨y, hy⟩ := ha; exact ⟨y, hy⟩)
          obtain ⟨m, hm⟩ := three_point T hF.1 (ι := Fin 3)
            ![W ∪ F a, F a', F a''] (by intro i; fin_cases i <;> simp [hU, hF.2.1])
            x1 x2 x3 (by
              intro i
              fin_cases i
              · exact Or.inr (Or.inl ⟨Or.inr hx1.1, Or.inl hx3.1⟩)
              · exact Or.inl ⟨hx1.2, hx2.1⟩
              · exact Or.inr (Or.inr ⟨hx2.2, hx3.2⟩))
          have m0 := Set.mem_iInter.1 hm 0
          have m1 := Set.mem_iInter.1 hm 1
          have m2 := Set.mem_iInter.1 hm 2
          simp at m0 m1 m2
          rcases m0 with m0 | m0
          · have : m ∈ W ∩ F a' := ⟨m0, m1⟩
            rw [e4] at this; exact this
          · have : m ∈ F a ∩ F a'' := ⟨m0, m2⟩
            rw [e3] at this; exact this
  | succ n ih =>
    intro a b q hlen hq W hW ha hb hint hind
    cases q with
    | nil => simp at hlen
    | @cons _ a' _ h q' =>
      have hq' : q'.IsPath := ((Walk.cons_isPath_iff h q').1 hq).1
      have hna : a ∉ q'.support := ((Walk.cons_isPath_iff h q').1 hq).2
      have haa' : a ≠ a' := h.ne
      have hlen' : q'.length = n + 2 := by simp at hlen; omega
      have e1 : (F a ∩ F a').Nonempty := (hF.2.2 a a' haa').1 h
      refine ih q' hlen' hq' (W ∪ F a)
        (SimpleGraph.induce_union_connected hW.preconnected (hF.2.1 a).preconnected
          (by obtain ⟨y, hy⟩ := ha; exact ⟨y, hy⟩)) ?_ ?_ ?_ ?_
      · obtain ⟨y, hy⟩ := e1
        exact ⟨y, Or.inr hy.1, hy.2⟩
      · obtain ⟨y, hy⟩ := hb
        exact ⟨y, Or.inl hy.1, hy.2⟩
      · intro x hx hxa' hxb
        have hxa : x ≠ a := fun e => hna (e ▸ hx)
        have h1 : W ∩ F x = ∅ := hint x (by simp [hx]) hxa hxb
        have h2 : F a ∩ F x = ∅ := by
          by_contra hne
          obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
          rcases hind a (by simp) x (by simp [hx]) ⟨y, hy⟩ with e | e
          · exact hxa e.symm
          · rw [Walk.edges_cons, List.mem_cons] at e
            rcases e with e | e
            · rw [Sym2.eq_iff] at e
              grind
            · exact hna (Walk.fst_mem_support_of_mem_edges q' e)
        rw [Set.union_inter_distrib_right, h1, h2]
        simp
      · intro x hx y hy hxy
        rcases hind x (by simp [hx]) y (by simp [hy]) hxy with e | e
        · exact Or.inl e
        · right
          rw [Walk.edges_cons, List.mem_cons] at e
          rcases e with e | e
          · rw [Sym2.eq_iff] at e
            exfalso
            grind
          · exact e

end ChordAux

theorem subtree_chordal {V : Type u} (G : SimpleGraph V)
    (hG : GavrilSubtree.Chordal.IsSubtreeGraph G) : GavrilSubtree.Chordal.IsChordal G := by
  obtain ⟨β, T, F, hF⟩ := hG
  intro u c hc hlen
  by_contra hno
  push Not at hno
  cases c with
  | nil => simp at hlen
  | @cons _ v _ h p =>
    rw [SimpleGraph.Walk.cons_isCycle_iff] at hc
    cases p with
    | nil => simp at hlen
    | @cons _ w _ h2 p' =>
      have hp := hc.1
      rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      obtain ⟨hp', hv⟩ := hp
      simp only [SimpleGraph.Walk.length_cons] at hlen
      refine ChordAux.key hF (p'.length - 2) p' (by omega) hp' (F v) (hF.2.1 v) ?_ ?_ ?_ ?_
      · exact (hF.2.2 v w h2.ne).1 h2
      · rw [Set.inter_comm]; exact (hF.2.2 u v h.ne).1 h
      · intro x hx hxw hxu
        by_contra hne
        obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
        have hxv : v ≠ x := fun e => hv (e ▸ hx)
        have hadj : G.Adj v x := (hF.2.2 v x hxv).2 ⟨y, hy⟩
        have := hno v (by simp) x (by simp [hx]) hadj
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at this
        rcases this with e | e | e
        · rw [Sym2.eq_iff] at e; grind
        · rw [Sym2.eq_iff] at e; grind
        · exact hv (SimpleGraph.Walk.fst_mem_support_of_mem_edges p' e)
      · intro x hx y hy hxy
        by_cases hxy' : x = y
        · exact Or.inl hxy'
        right
        have hadj : G.Adj x y := (hF.2.2 x y hxy').2 hxy
        have := hno x (by simp [hx]) y (by simp [hy]) hadj
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at this
        rcases this with e | e | e
        · rw [Sym2.eq_iff] at e; exfalso; grind
        · rw [Sym2.eq_iff] at e; exfalso; grind
        · exact e

namespace DiracAux

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

lemma two_le_length {u w : V} (b : G.Walk u w) (h : G.Adj u w) (he : s(u, w) ∉ b.edges) :
    2 ≤ b.length := by
  cases b with
  | nil => exact absurd rfl h.ne
  | cons h' b' =>
    cases b' with
    | nil => simp at he
    | cons h'' b'' => simp

lemma shortcut {s t x y : V} (p : G.Walk s t) (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : G.Adj x y) (he : s(x, y) ∉ p.edges) :
    ∃ p' : G.Walk s t, p'.length < p.length ∧ ∀ z ∈ p'.support, z ∈ p.support := by
  obtain ⟨a1, a2, rfl⟩ := p.mem_support_iff_exists_append.mp hx
  rw [Walk.mem_support_append_iff] at hy
  rcases hy with hy | hy
  · obtain ⟨b, r, rfl⟩ := a1.mem_support_iff_exists_append.mp hy
    have h2 := two_le_length r hxy.symm (by
      intro h; apply he; simp [Walk.edges_append, Sym2.eq_swap] at h ⊢; tauto)
    refine ⟨b.append (Walk.cons hxy.symm a2), ?_, ?_⟩
    · simp [Walk.length_append]; omega
    · intro z hz
      simp only [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hz ⊢
      have := r.start_mem_support
      rcases hz with hz | rfl | hz <;> tauto
  · obtain ⟨b, r, rfl⟩ := a2.mem_support_iff_exists_append.mp hy
    have h2 := two_le_length b hxy (by
      intro h; apply he; simp [Walk.edges_append] at h ⊢; tauto)
    refine ⟨a1.append (Walk.cons hxy r), ?_, ?_⟩
    · simp [Walk.length_append]; omega
    · intro z hz
      simp only [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hz ⊢
      have := b.start_mem_support
      rcases hz with hz | rfl | hz <;> tauto

lemma clique_of_path (hG : GavrilSubtree.Chordal.IsChordal G) (v : V) (K : Set V)
    (hK : ∀ x ∈ K, x ≠ v ∧ ¬ G.Adj v x) :
    ∀ (n : ℕ) (s t : V) (p : G.Walk s t), p.length = n → p.IsPath → s ≠ t → G.Adj v s →
      G.Adj v t → (∀ y ∈ p.support, y = s ∨ y = t ∨ y ∈ K) → G.Adj s t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s t p hn hp hst hs ht hsupp
  classical
  by_cases h1 : p.length = 1
  · exact Walk.adj_of_length_eq_one h1
  have h0 : p.length ≠ 0 := fun h => hst (Walk.eq_of_length_eq_zero h)
  have hvp : v ∉ p.support := by
    intro hv
    rcases hsupp v hv with h | h | h
    · exact hs.ne h
    · exact ht.ne h
    · exact (hK v h).1 rfl
  set c : G.Walk s s := Walk.cons hs.symm (Walk.cons ht p.reverse) with hc
  have hcyc : c.IsCycle := by
    rw [hc, Walk.cons_isCycle_iff, Walk.cons_isPath_iff]
    refine ⟨⟨hp.reverse, by simpa using hvp⟩, ?_⟩
    simp only [Walk.edges_cons, Walk.edges_reverse, List.mem_cons, List.mem_reverse, not_or]
    refine ⟨?_, ?_⟩
    · intro h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h, _⟩
      · exact hst (h1.trans h2)
      · exact hst h
    · intro h
      exact hvp (p.snd_mem_support_of_mem_edges h)
  have hlen : 4 ≤ c.length := by
    simp [hc]; omega
  obtain ⟨x, hx, y, hy, hxy, hne⟩ := hG s c hcyc hlen
  have hcs : ∀ z ∈ c.support, z = v ∨ z ∈ p.support := by
    intro z hz
    simp only [hc, Walk.support_cons, Walk.support_reverse, List.mem_cons, List.mem_reverse] at hz
    rcases hz with h | h | h
    · right; rw [h]; exact p.start_mem_support
    · left; exact h
    · right; exact h
  have hedges : ∀ e ∈ p.edges, e ∈ c.edges := by
    intro e he
    simp [hc, he]
  have hv : ∀ y ∈ p.support, G.Adj v y → s(v, y) ∈ c.edges := by
    intro y hy hvy
    rcases hsupp y hy with h | h | h
    · subst h; simp [hc, Sym2.eq_swap]
    · subst h; simp [hc]
    · exact absurd hvy (hK y h).2
  rcases hcs x hx with rfl | hxp
  · rcases hcs y hy with rfl | hyp
    · exact absurd hxy (G.loopless.irrefl _)
    · exact absurd (hv y hyp hxy) hne
  rcases hcs y hy with rfl | hyp
  · exact absurd (by rw [Sym2.eq_swap]; exact hv x hxp hxy.symm) hne
  have hne' : s(x, y) ∉ p.edges := fun h => hne (hedges _ h)
  obtain ⟨p', hlt, hsub⟩ := shortcut p hxp hyp hxy hne'
  have hb := p'.bypass_isPath
  exact ih p'.bypass.length (lt_of_le_of_lt p'.length_bypass_le_length (hn ▸ hlt)) s t _ rfl hb
    hst hs ht (fun z hz => hsupp z (hsub z (p'.support_bypass_subset_support hz)))

/-- `a` is simplicial inside the vertex set `A`. -/
def Simp (G : SimpleGraph V) (A : Finset V) (a : V) : Prop :=
  ∀ y ∈ A, ∀ z ∈ A, G.Adj a y → G.Adj a z → y ≠ z → G.Adj y z

lemma dirac_aux (hG : GavrilSubtree.Chordal.IsChordal G) : ∀ (n : ℕ) (A : Finset V),
    A.card = n → (∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y) ∨
    ∃ a ∈ A, ∃ b ∈ A, ¬ G.Adj a b ∧ a ≠ b ∧ Simp G A a ∧ Simp G A b := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn
  by_cases hcl : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y
  · exact Or.inl hcl
  right
  push Not at hcl
  obtain ⟨v, hv, u, hu, hvu, hnadj⟩ := hcl
  obtain ⟨K, hKdef⟩ : ∃ K : Set V, ∀ x, x ∈ K ↔ x ∈ A ∧ x ≠ v ∧ ¬ G.Adj v x :=
    ⟨{x | x ∈ A ∧ x ≠ v ∧ ¬ G.Adj v x}, fun x => Iff.rfl⟩
  have hKv : ∀ x ∈ K, x ≠ v ∧ ¬ G.Adj v x := fun x hx => ((hKdef x).1 hx).2
  have hKA : ∀ x ∈ K, x ∈ A := fun x hx => ((hKdef x).1 hx).1
  have huK : u ∈ K := (hKdef u).2 ⟨hu, hvu.symm, hnadj⟩
  obtain ⟨C, hCdef⟩ : ∃ C : Finset V, ∀ x, x ∈ C ↔
      x ∈ A ∧ ∃ p : G.Walk u x, ∀ y ∈ p.support, y ∈ K :=
    ⟨A.filter (fun x => ∃ p : G.Walk u x, ∀ y ∈ p.support, y ∈ K), by simp⟩
  have huC : u ∈ C := (hCdef u).2 ⟨hu, Walk.nil, by simpa using huK⟩
  have hCK : ∀ x ∈ C, x ∈ K := by
    intro x hx
    obtain ⟨_, p, hp⟩ := (hCdef x).1 hx
    exact hp x p.end_mem_support
  have hCA : ∀ x ∈ C, x ∈ A := fun x hx => ((hCdef x).1 hx).1
  have hCext : ∀ x ∈ C, ∀ y ∈ K, G.Adj x y → y ∈ C := by
    intro x hx y hy hxy
    obtain ⟨_, p, hp⟩ := (hCdef x).1 hx
    refine (hCdef y).2 ⟨hKA y hy, p.concat hxy, ?_⟩
    intro z hz
    simp only [Walk.support_concat, List.mem_append,
      List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hp z hz
    · exact hy
  obtain ⟨NC, hNCdef⟩ : ∃ NC : Finset V, ∀ x, x ∈ NC ↔
      x ∈ A ∧ x ∉ C ∧ ∃ c ∈ C, G.Adj c x :=
    ⟨A.filter (fun x => x ∉ C ∧ ∃ c ∈ C, G.Adj c x), by simp⟩
  have hNCv : ∀ x ∈ NC, G.Adj v x := by
    intro x hx
    obtain ⟨hxA, hxC, c, hc, hcx⟩ := (hNCdef x).1 hx
    by_contra hvx
    have hxv : x ≠ v := by
      rintro rfl
      exact (hKv c (hCK c hc)).2 hcx.symm
    exact hxC (hCext c hc x ((hKdef x).2 ⟨hxA, hxv, hvx⟩) hcx)
  have hnbr : ∀ c ∈ C, ∀ y ∈ A, G.Adj c y → y ∈ C ∨ y ∈ NC := by
    intro c hc y hy hcy
    by_cases hyC : y ∈ C
    · exact Or.inl hyC
    · exact Or.inr ((hNCdef y).2 ⟨hy, hyC, c, hc, hcy⟩)
  have hNCclique : ∀ s ∈ NC, ∀ t ∈ NC, s ≠ t → G.Adj s t := by
    intro s hs t ht hst
    obtain ⟨hsA, hsC, c1, hc1, hc1s⟩ := (hNCdef s).1 hs
    obtain ⟨htA, htC, c2, hc2, hc2t⟩ := (hNCdef t).1 ht
    obtain ⟨_, w1, hw1⟩ := (hCdef c1).1 hc1
    obtain ⟨_, w2, hw2⟩ := (hCdef c2).1 hc2
    let P : G.Walk s t := Walk.cons hc1s.symm ((w1.reverse.append w2).concat hc2t)
    have hP : ∀ y ∈ P.support, y = s ∨ y = t ∨ y ∈ K := by
      intro y hy
      simp only [P, Walk.support_cons, Walk.support_concat, Walk.support_append,
        Walk.support_reverse, List.concat_eq_append, List.mem_cons, List.mem_append,
        List.mem_reverse, List.mem_singleton] at hy
      rcases hy with h | (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (hw1 y h))
      · exact Or.inr (Or.inr (hw2 y (List.mem_of_mem_tail h)))
      · exact Or.inr (Or.inl (by simpa using h))
    have := clique_of_path hG v K hKv _ s t P.bypass rfl P.bypass_isPath hst (hNCv s hs)
      (hNCv t ht) (fun y hy => hP y (P.support_bypass_subset_support hy))
    exact this
  have hSimpC : ∀ a ∈ C, Simp G (C ∪ NC) a → Simp G A a := by
    intro a ha hs y hy z hz hay haz hyz
    rcases hnbr a ha y hy hay with h1 | h1 <;> rcases hnbr a ha z hz haz with h2 | h2 <;>
      exact hs y (by simp [h1]) z (by simp [h2]) hay haz hyz
  have hCNCsub : C ∪ NC ⊆ A := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact hCA x h
    · exact ((hNCdef x).1 h).1
  have hvC : v ∉ C := fun h => (hKv v (hCK v h)).1 rfl
  have hvNC : v ∉ NC := fun h => G.loopless.irrefl _ (hNCv v h)
  have h1 : (C ∪ NC).card < n := by
    rw [← hn]
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hCNCsub).2 ⟨v, hv, ?_⟩)
    simp [hvC, hvNC]
  have h2 : (A \ C).card < n := by
    rw [← hn]
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset Finset.sdiff_subset).2
      ⟨u, hu, ?_⟩)
    simp [huC]
  -- a simplicial vertex in `C`
  obtain ⟨a, haC, haS⟩ : ∃ a ∈ C, Simp G A a := by
    rcases ih _ h1 (C ∪ NC) rfl with hcl1 | ⟨a1, ha1, b1, hb1, hnab, hne, hs1, hs2⟩
    · refine ⟨u, huC, hSimpC u huC ?_⟩
      intro y hy z hz _ _ hyz
      exact hcl1 y hy z hz hyz
    · by_cases h : a1 ∈ C
      · exact ⟨a1, h, hSimpC a1 h hs1⟩
      · by_cases h' : b1 ∈ C
        · exact ⟨b1, h', hSimpC b1 h' hs2⟩
        · exfalso
          have hx : a1 ∈ NC := by
            rcases Finset.mem_union.1 ha1 with h'' | h''
            · exact absurd h'' h
            · exact h''
          have hy : b1 ∈ NC := by
            rcases Finset.mem_union.1 hb1 with h'' | h''
            · exact absurd h'' h'
            · exact h''
          exact hnab (hNCclique a1 hx b1 hy hne)
  -- a simplicial vertex outside `C ∪ NC`
  have hSimpB : ∀ b ∈ A \ C, b ∉ NC → Simp G (A \ C) b → Simp G A b := by
    intro b hb hbNC hs y hy z hz hby hbz hyz
    have hbA : b ∈ A := (Finset.mem_sdiff.1 hb).1
    have hbC : b ∉ C := (Finset.mem_sdiff.1 hb).2
    have hyC : y ∉ C := fun h => hbNC ((hNCdef b).2 ⟨hbA, hbC, y, h, hby.symm⟩)
    have hzC : z ∉ C := fun h => hbNC ((hNCdef b).2 ⟨hbA, hbC, z, h, hbz.symm⟩)
    exact hs y (Finset.mem_sdiff.2 ⟨hy, hyC⟩) z (Finset.mem_sdiff.2 ⟨hz, hzC⟩) hby hbz hyz
  obtain ⟨b, hbB, hbNC, hbS⟩ : ∃ b ∈ A \ C, b ∉ NC ∧ Simp G A b := by
    rcases ih _ h2 (A \ C) rfl with hcl2 | ⟨a2, ha2, b2, hb2, hnab, hne, hs1, hs2⟩
    · refine ⟨v, Finset.mem_sdiff.2 ⟨hv, hvC⟩, hvNC, ?_⟩
      intro y hy z hz hvy hvz hyz
      have hyC : y ∉ C := fun h => (hKv y (hCK y h)).2 hvy
      have hzC : z ∉ C := fun h => (hKv z (hCK z h)).2 hvz
      exact hcl2 y (Finset.mem_sdiff.2 ⟨hy, hyC⟩) z (Finset.mem_sdiff.2 ⟨hz, hzC⟩) hyz
    · by_cases h : a2 ∈ NC
      · by_cases h' : b2 ∈ NC
        · exact absurd (hNCclique a2 h b2 h' hne) hnab
        · exact ⟨b2, hb2, h', hSimpB b2 hb2 h' hs2⟩
      · exact ⟨a2, ha2, h, hSimpB a2 ha2 h hs1⟩
  have hbA : b ∈ A := (Finset.mem_sdiff.1 hbB).1
  have hbC : b ∉ C := (Finset.mem_sdiff.1 hbB).2
  refine ⟨a, hCA a haC, b, hbA, ?_, ?_, haS, hbS⟩
  · intro h
    exact hbNC ((hNCdef b).2 ⟨hbA, hbC, a, haC, h⟩)
  · rintro rfl
    exact hbC haC

end DiracAux

end AlphaOmegaAux

namespace AlphaOmegaAux

open SimpleGraph

theorem main {V : Type u} [Finite V] (G : SimpleGraph V) (hG : GavrilSubtree.Chordal.IsChordal G) :
    ∀ (n : ℕ) (A : Finset V), A.card = n →
      ∃ I : Finset V, I ⊆ A ∧ G.IsIndepSet (I : Set V) ∧ A.card ≤ I.card * G.cliqueNum := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn
  rcases DiracAux.dirac_aux hG n A hn with hcl | ⟨a, ha, b, hb, hnab, hne, hSa, hSb⟩
  · have hcliq : G.IsClique (A : Set V) := fun x hx y hy hxy => hcl x hx y hy hxy
    have hle : A.card ≤ G.cliqueNum :=
      SimpleGraph.IsClique.card_le_cliqueNum (G := G) (tc := hcliq)
    rcases A.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · exact ⟨∅, by simp, by simp, by simp⟩
    · refine ⟨{v}, by simpa using hv, by simp, ?_⟩
      simpa using hle
  · set N : Finset V := A.filter (fun y => y = a ∨ G.Adj a y) with hN
    have hNcl : G.IsClique (N : Set V) := by
      intro x hx y hy hxy
      simp only [hN, Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      rcases hx with ⟨hxA, rfl | hax⟩
      · rcases hy with ⟨hyA, rfl | hay⟩
        · exact absurd rfl hxy
        · exact hay
      · rcases hy with ⟨hyA, rfl | hay⟩
        · exact hax.symm
        · exact hSa x hxA y hyA hax hay hxy
    have hNle : N.card ≤ G.cliqueNum :=
      SimpleGraph.IsClique.card_le_cliqueNum (G := G) (tc := hNcl)
    have haN : a ∈ N := by simp [hN, ha]
    have hlt : (A \ N).card < n := by
      rw [← hn]
      exact Finset.card_lt_card (Finset.sdiff_ssubset (Finset.filter_subset _ _) ⟨a, haN⟩)
    obtain ⟨I', hI'sub, hI'ind, hI'card⟩ := ih _ hlt (A \ N) rfl
    have haI' : a ∉ I' := fun h => (Finset.mem_sdiff.1 (hI'sub h)).2 haN
    have hnadj : ∀ y ∈ I', ¬ G.Adj a y := by
      intro y hy hadj
      have := Finset.mem_sdiff.1 (hI'sub hy)
      exact this.2 (by simp [hN, this.1, hadj])
    refine ⟨insert a I', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ha
      · exact (Finset.mem_sdiff.1 (hI'sub hx)).1
    · rw [Finset.coe_insert]
      refine hI'ind.insert ?_
      intro y hy _
      exact ⟨hnadj y hy, fun h => hnadj y hy h.symm⟩
    · rw [Finset.card_insert_of_notMem haI']
      have h1 : A.card = N.card + (A \ N).card := by
        have := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun y => y = a ∨ G.Adj a y) A)
        rw [hN]
        omega
      calc A.card = N.card + (A \ N).card := h1
        _ ≤ G.cliqueNum + I'.card * G.cliqueNum := Nat.add_le_add hNle hI'card
        _ = (I'.card + 1) * G.cliqueNum := by rw [Nat.add_mul, one_mul, Nat.add_comm]

end AlphaOmegaAux

theorem solution {W β : Type} [Fintype W]
    (H : SimpleGraph W) (T : SimpleGraph β) (F : W → Set β)
    (hF : GavrilSubtree.Chordal.IsSubtreeRep H T F) :
    Fintype.card W ≤ H.indepNum * H.cliqueNum := by
  classical
  have hchord := AlphaOmegaAux.subtree_chordal H ⟨β, T, F, hF⟩
  obtain ⟨I, -, hI, hcard⟩ := AlphaOmegaAux.main H hchord _ (Finset.univ : Finset W) rfl
  have h1 : I.card ≤ H.indepNum := hI.card_le_indepNum
  rw [Finset.card_univ] at hcard
  exact hcard.trans (Nat.mul_le_mul_right _ h1)

