-- Prove2me | solution 1 for PathsTreesFlowers.Duality.Supplement.augmenting_tree_4_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:31.036134+00:00
-- url     : https://prove2.me/submissions/027e36b5-0ff2-40fa-8e2b-47c4d8dbbf64

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Supplement_Trees

open PathsTreesFlowers
open PathsTreesFlowers.Duality
open PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMatching G M) (J : AltTree G) (r : V) (e : E) (u v : V)
    (hA : IsAugmentingTree G M J r e u v) :
    ∃ vs es, PathIn G (adjoinEdge G J.toSub e u v hA.2.2.2.2) r v vs es ∧
      (∀ ws fs, PathIn G (adjoinEdge G J.toSub e u v hA.2.2.2.2) r v ws fs →
        ws = vs ∧ fs = es) ∧
      IsAlternatingPath G M vs es ∧ 0 < es.length ∧
      IsExposed G M r ∧ IsExposed G M v := by
        classical
        obtain ⟨hP, huO, hvJ, hvexp, he⟩ := hA
        obtain ⟨hmax, hrJ, hrJexp, hrexp⟩ := hP
        have hdisj : ∀ x, x ∈ J.inner → x ∉ J.outer := fun x hx => Finset.disjoint_left.mp J.disjoint hx
        have hmemT : ∀ f ∈ J.edges, ∀ x, x ∈ G.ends f → x ∈ J.inner ∪ J.outer := by
          intro f hf x hx
          exact Finset.mem_sym2_iff.mp (J.toSub.edges_sub f hf) x hx
        have hside : ∀ f ∈ J.edges, ∀ x y, G.ends f = s(x, y) →
            (x ∈ J.inner ∧ y ∈ J.outer) ∨ (x ∈ J.outer ∧ y ∈ J.inner) := by
          intro f hf x y hxy
          obtain ⟨a, ha, b, hb, h⟩ := J.edge_ends f hf
          rw [hxy, Sym2.eq_iff] at h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨ha, hb⟩
          · exact Or.inr ⟨hb, ha⟩
        have hother : ∀ f ∈ J.edges, ∀ w ∈ J.inner, w ∈ G.ends f → ∃ a ∈ J.outer, G.ends f = s(w, a) := by
          intro f hf w hw hwf
          obtain ⟨a, ha, b, hb, h⟩ := J.edge_ends f hf
          rw [h, Sym2.mem_iff] at hwf
          rcases hwf with rfl | rfl
          · exact ⟨b, hb, h⟩
          · exact absurd hb (hdisj _ hw)
        obtain ⟨H, hHadj⟩ : ∃ H : SimpleGraph {x // x ∈ J.inner ∪ J.outer},
            ∀ a b, H.Adj a b ↔ ∃ f ∈ J.edges, G.ends f = s(a.1, b.1) := by
          refine ⟨SimpleGraph.fromRel (fun a b => ∃ f ∈ J.edges, G.ends f = s(a.1, b.1)), ?_⟩
          intro a b
          rw [SimpleGraph.fromRel_adj]
          constructor
          · rintro ⟨_, h | ⟨f, hf, hfe⟩⟩
            · exact h
            · exact ⟨f, hf, by rw [hfe, Sym2.eq_swap]⟩
          · rintro ⟨f, hf, hfe⟩
            refine ⟨?_, Or.inl ⟨f, hf, hfe⟩⟩
            rintro rfl
            exact G.loopless f (by rw [hfe]; exact Sym2.mk_isDiag_iff.mpr rfl)
        have hreach : ∀ x y, Relation.ReflTransGen (fun a b => ∃ e ∈ J.edges, G.ends e = s(a, b)) x y →
            ∀ hx : x ∈ J.inner ∪ J.outer, ∃ hy : y ∈ J.inner ∪ J.outer, H.Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
          intro x y h hx
          induction h with
          | refl => exact ⟨hx, SimpleGraph.Reachable.refl _⟩
          | tail _ hbc ih =>
            obtain ⟨hb, hr⟩ := ih
            obtain ⟨f, hf, hfe⟩ := hbc
            have hc := hmemT f hf _ (by rw [hfe]; exact Sym2.mem_mk_right _ _)
            exact ⟨hc, hr.trans ((hHadj _ ⟨_, hc⟩).mpr ⟨f, hf, hfe⟩).reachable⟩
        have hconn : H.Connected := by
          have hne : Nonempty {x // x ∈ J.inner ∪ J.outer} := by
            obtain ⟨x, hx⟩ := J.connected.1; exact ⟨⟨x, hx⟩⟩
          refine SimpleGraph.Connected.mk (fun a b => ?_)
          obtain ⟨hb, h⟩ := hreach a.1 b.1 (J.connected.2 a.1 a.2 b.1 b.2) a.2
          exact h
        have hψ : ∀ s ∈ H.edgeSet, ∃ f ∈ J.edges, G.ends f = Sym2.map Subtype.val s := by
          intro s hs
          induction s using Sym2.ind with
          | h a b =>
            obtain ⟨f, hf, hfe⟩ := (hHadj a b).mp ((SimpleGraph.mem_edgeSet H).mp hs)
            exact ⟨f, hf, by simp [hfe]⟩
        obtain ⟨ψ, hψJ, hψe⟩ : ∃ ψ : H.edgeSet → E, (∀ s, ψ s ∈ J.edges) ∧
            ∀ s, G.ends (ψ s) = Sym2.map Subtype.val s.1 :=
          ⟨fun s => Classical.choose (hψ s.1 s.2), fun s => (Classical.choose_spec (hψ s.1 s.2)).1,
            fun s => (Classical.choose_spec (hψ s.1 s.2)).2⟩
        let ψ' : H.edgeSet → {f // f ∈ J.edges} := fun s => ⟨ψ s, hψJ s⟩
        have hψinj : Function.Injective ψ' := by
          intro s t hst
          have h0 : ψ s = ψ t := congrArg Subtype.val hst
          apply Subtype.ext
          apply Sym2.map.injective Subtype.val_injective
          rw [← hψe s, ← hψe t, h0]
        have hcardJ : Nat.card {f // f ∈ J.edges} = J.edges.card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        have hcardW : Nat.card {x // x ∈ J.inner ∪ J.outer} = J.edges.card + 1 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact J.card_verts
        have hle := Nat.card_le_card_of_injective ψ' hψinj
        have hge := hconn.card_vert_le_card_edgeSet_add_one
        have htree : H.IsTree := SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconn, by omega⟩
        have hacyc := htree.isAcyclic
        have hψbij := hψinj.bijective_of_nat_card_le (by omega)
        have hinj : ∀ f1 ∈ J.edges, ∀ f2 ∈ J.edges, G.ends f1 = G.ends f2 → f1 = f2 := by
          intro f1 hf1 f2 hf2 h12
          obtain ⟨s1, hs1⟩ := hψbij.2 ⟨f1, hf1⟩
          obtain ⟨s2, hs2⟩ := hψbij.2 ⟨f2, hf2⟩
          have e1 : ψ s1 = f1 := congrArg Subtype.val hs1
          have e2 : ψ s2 = f2 := congrArg Subtype.val hs2
          have : s1 = s2 := by
            apply Subtype.ext
            apply Sym2.map.injective Subtype.val_injective
            rw [← hψe, ← hψe, e1, e2, h12]
          rw [← e1, ← e2, this]
        have hcons : ∀ (a b : V) (l : List V) (f : E) (fs : List E),
            IsPath G (a :: b :: l) (f :: fs) ↔ (a ∉ b :: l ∧ G.ends f = s(a, b) ∧ IsPath G (b :: l) fs) := by
          intro a b l f fs
          simp only [IsPath, List.nodup_cons, List.length_cons, List.map_cons, List.tail_cons,
            List.zipWith_cons_cons, List.cons.injEq, List.mem_cons]
          constructor
          · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
            exact ⟨h1, h5, ⟨h2, h3⟩, by omega, h6⟩
          · rintro ⟨h1, h5, ⟨h2, h3⟩, h4, h6⟩
            exact ⟨⟨h1, h2, h3⟩, by omega, h5, h6⟩
        have hmapinj : ∀ es fs : List E, es.toFinset ⊆ J.edges → fs.toFinset ⊆ J.edges →
            es.map G.ends = fs.map G.ends → es = fs := by
          intro es
          induction es with
          | nil => intro fs _ _ h; simp at h; simp [h]
          | cons a es ih =>
            intro fs h1 h2 h
            cases fs with
            | nil => simp at h
            | cons b fs =>
              simp only [List.map_cons, List.cons.injEq] at h
              have ha : a ∈ J.edges := h1 (by simp)
              have hb : b ∈ J.edges := h2 (by simp)
              rw [hinj a ha b hb h.1, ih fs (fun x hx => h1 (by simp at hx ⊢; tauto))
                (fun x hx => h2 (by simp at hx ⊢; tauto)) h.2]
        have hW2L : ∀ (a b : {x // x ∈ J.inner ∪ J.outer}) (p : H.Walk a b), p.IsPath →
            ∃ vs es, IsPath G vs es ∧ vs = p.support.map Subtype.val ∧ es.toFinset ⊆ J.edges ∧
              vs.head? = some a.1 ∧ vs.getLast? = some b.1 := by
          intro a b p hp
          induction p with
          | @nil w => exact ⟨[w.1], [], by simp [IsPath], by simp, by simp, by simp, by simp⟩
          | @cons x y z h p ih =>
            rw [SimpleGraph.Walk.cons_isPath_iff] at hp
            obtain ⟨vs, es, h1, h2, h3, h4, h5⟩ := ih hp.1
            obtain ⟨f, hf, hfe⟩ := (hHadj _ _).mp h
            cases vs with
            | nil => simp at h4
            | cons t tl =>
              simp only [List.head?_cons, Option.some.injEq] at h4
              subst h4
              refine ⟨x.1 :: y.1 :: tl, f :: es, (hcons _ _ _ _ _).mpr ⟨?_, hfe, h1⟩, ?_, ?_, by simp, ?_⟩
              · rw [h2]; intro hx
                rw [List.mem_map] at hx
                obtain ⟨w, hw, hwx⟩ := hx
                exact hp.2 (Subtype.ext hwx ▸ hw)
              · simp [h2]
              · intro g hg; simp at hg; rcases hg with rfl | hg
                · exact hf
                · exact h3 (by simpa using hg)
              · rw [List.getLast?_cons_cons]; exact h5
        have hL2W : ∀ (vs : List V) (es : List E) (a b : V) (ha : a ∈ J.inner ∪ J.outer)
            (hb : b ∈ J.inner ∪ J.outer), IsPath G vs es → vs.toFinset ⊆ J.inner ∪ J.outer →
            es.toFinset ⊆ J.edges → vs.head? = some a → vs.getLast? = some b →
            ∃ p : H.Walk ⟨a, ha⟩ ⟨b, hb⟩, p.support.map Subtype.val = vs := by
          intro vs
          induction vs with
          | nil => intro es a b ha hb _ _ _ h; simp at h
          | cons x rest ih =>
            intro es a b ha hb hpath hvs hes hhead hlast
            simp only [List.head?_cons, Option.some.injEq] at hhead
            subst hhead
            cases rest with
            | nil =>
              simp only [List.getLast?_singleton, Option.some.injEq] at hlast
              subst hlast
              exact ⟨SimpleGraph.Walk.nil, by simp⟩
            | cons y rest' =>
              cases es with
              | nil => exact absurd hpath.2.1 (by simp)
              | cons f es' =>
                obtain ⟨hx, hfe, hp'⟩ := (hcons _ _ _ _ _).mp hpath
                have hy : y ∈ J.inner ∪ J.outer := hvs (by simp)
                obtain ⟨p, hp⟩ := ih es' y b hy hb hp'
                  (fun z hz => hvs (by simp at hz ⊢; tauto)) (fun g hg => hes (by simp at hg ⊢; tauto))
                  rfl (by rwa [List.getLast?_cons_cons] at hlast)
                have hf : f ∈ J.edges := hes (by simp)
                exact ⟨SimpleGraph.Walk.cons ((hHadj ⟨x, ha⟩ ⟨y, hy⟩).mpr ⟨f, hf, hfe⟩) p, by simp [hp]⟩
        have huniqJ : ∀ a b vs es ws fs, PathIn G J.toSub a b vs es → PathIn G J.toSub a b ws fs →
            vs = ws ∧ es = fs := by
          intro a b vs es ws fs h1 h2
          obtain ⟨hp1, hv1, he1, hh1, hl1⟩ := h1
          obtain ⟨hp2, hv2, he2, hh2, hl2⟩ := h2
          have ha : a ∈ J.inner ∪ J.outer := hv1 (List.mem_toFinset.mpr (List.mem_of_mem_head? hh1))
          have hb : b ∈ J.inner ∪ J.outer := hv1 (List.mem_toFinset.mpr (List.mem_of_mem_getLast? hl1))
          obtain ⟨p, hp⟩ := hL2W vs es a b ha hb hp1 hv1 he1 hh1 hl1
          obtain ⟨q, hq⟩ := hL2W ws fs a b ha hb hp2 hv2 he2 hh2 hl2
          have hpP : p.IsPath := SimpleGraph.Walk.IsPath.mk' (List.Nodup.of_map Subtype.val (hp ▸ hp1.1))
          have hqP : q.IsPath := SimpleGraph.Walk.IsPath.mk' (List.Nodup.of_map Subtype.val (hq ▸ hp2.1))
          have hpq : p = q := congrArg Subtype.val (hacyc.path_unique ⟨p, hpP⟩ ⟨q, hqP⟩)
          have hvw : vs = ws := by rw [← hp, ← hq, hpq]
          refine ⟨hvw, hmapinj es fs he1 he2 ?_⟩
          rw [hp1.2.2, hp2.2.2, hvw]
        have hadjside : ∀ a b : {x // x ∈ J.inner ∪ J.outer}, H.Adj a b → (a.1 ∈ J.outer ↔ b.1 ∉ J.outer) := by
          intro a b h
          obtain ⟨f, hf, hfe⟩ := (hHadj a b).mp h
          rcases hside f hf _ _ hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨fun h => absurd h (hdisj _ h1), fun h => absurd h2 h⟩
          · exact ⟨fun _ => hdisj _ h2, fun _ => h1⟩
        have hparity : ∀ (a b : {x // x ∈ J.inner ∪ J.outer}) (p : H.Walk a b),
            (p.length % 2 = 0 ↔ (a.1 ∈ J.outer ↔ b.1 ∈ J.outer)) := by
          intro a b p
          induction p with
          | nil => simp
          | @cons x y z h p ih =>
            have := hadjside x y h
            rw [SimpleGraph.Walk.length_cons]
            constructor
            · intro h2
              have : ¬ p.length % 2 = 0 := by omega
              tauto
            · intro h2
              by_contra h3
              have : p.length % 2 = 0 := by omega
              tauto
        have hdistpar : ∀ o x : {x // x ∈ J.inner ∪ J.outer},
            (H.dist o x % 2 = 0 ↔ (o.1 ∈ J.outer ↔ x.1 ∈ J.outer)) := by
          intro o x
          obtain ⟨p, hp⟩ := (hconn.preconnected o x).exists_walk_length_eq_dist
          rw [← hp]; exact hparity o x p
        have hpar : ∀ (o x1 x2 y : {x // x ∈ J.inner ∪ J.outer}), H.Adj x1 y → H.Adj x2 y →
            H.dist o x1 + 1 = H.dist o y → H.dist o x2 + 1 = H.dist o y → x1 = x2 := by
          intro o x1 x2 y h1 h2 d1 d2
          obtain ⟨p1, hp1⟩ := (hconn.preconnected o x1).exists_walk_length_eq_dist
          obtain ⟨p2, hp2⟩ := (hconn.preconnected o x2).exists_walk_length_eq_dist
          have hq1 : (p1.concat h1).IsPath :=
            (p1.concat h1).isPath_of_length_eq_dist (by rw [SimpleGraph.Walk.length_concat]; omega)
          have hq2 : (p2.concat h2).IsPath :=
            (p2.concat h2).isPath_of_length_eq_dist (by rw [SimpleGraph.Walk.length_concat]; omega)
          have := congrArg Subtype.val (hacyc.path_unique ⟨_, hq1⟩ ⟨_, hq2⟩)
          obtain ⟨hv, _⟩ := SimpleGraph.Walk.concat_inj this
          exact hv
        have hrT : r ∈ J.inner ∪ J.outer := hrJ
        have hchild : ∀ w ∈ J.inner, ∃ f ∈ J.edges, ∃ a ∈ J.outer, G.ends f = s(w, a) ∧
            ∀ (hw : w ∈ J.inner ∪ J.outer) (ha : a ∈ J.inner ∪ J.outer),
              H.dist ⟨r, hrT⟩ ⟨w, hw⟩ + 1 = H.dist ⟨r, hrT⟩ ⟨a, ha⟩ := by
          intro w hw
          have hwT : w ∈ J.inner ∪ J.outer := Finset.mem_union_left _ hw
          obtain ⟨f1, f2, hne, hfs⟩ := Finset.card_eq_two.mp (J.inner_deg w hw)
          have hf1 : f1 ∈ J.edges.filter (fun e => w ∈ G.ends e) := by rw [hfs]; simp
          have hf2 : f2 ∈ J.edges.filter (fun e => w ∈ G.ends e) := by rw [hfs]; simp
          rw [Finset.mem_filter] at hf1 hf2
          obtain ⟨a1, ha1, he1⟩ := hother f1 hf1.1 w hw hf1.2
          obtain ⟨a2, ha2, he2⟩ := hother f2 hf2.1 w hw hf2.2
          have ha1T : a1 ∈ J.inner ∪ J.outer := Finset.mem_union_right _ ha1
          have ha2T : a2 ∈ J.inner ∪ J.outer := Finset.mem_union_right _ ha2
          have hadj1 : H.Adj ⟨a1, ha1T⟩ ⟨w, hwT⟩ :=
            (hHadj _ _).mpr ⟨f1, hf1.1, by rw [he1, Sym2.eq_swap]⟩
          have hadj2 : H.Adj ⟨a2, ha2T⟩ ⟨w, hwT⟩ :=
            (hHadj _ _).mpr ⟨f2, hf2.1, by rw [he2, Sym2.eq_swap]⟩
          have hwO : w ∉ J.outer := hdisj w hw
          have P1 : (H.dist ⟨r, hrT⟩ ⟨a1, ha1T⟩ % 2 = 0 ↔ r ∈ J.outer) := by
            rw [hdistpar]; simp [ha1]
          have P2 : (H.dist ⟨r, hrT⟩ ⟨a2, ha2T⟩ % 2 = 0 ↔ r ∈ J.outer) := by
            rw [hdistpar]; simp [ha2]
          have Pw : (H.dist ⟨r, hrT⟩ ⟨w, hwT⟩ % 2 = 0 ↔ r ∉ J.outer) := by
            rw [hdistpar]; simp [hwO]
          have hd1 := hadj1.symm.diff_dist_adj (u := ⟨r, hrT⟩)
          have hd2 := hadj2.symm.diff_dist_adj (u := ⟨r, hrT⟩)
          by_cases c1 : H.dist ⟨r, hrT⟩ ⟨w, hwT⟩ + 1 = H.dist ⟨r, hrT⟩ ⟨a1, ha1T⟩
          · exact ⟨f1, hf1.1, a1, ha1, he1, fun _ _ => c1⟩
          by_cases c2 : H.dist ⟨r, hrT⟩ ⟨w, hwT⟩ + 1 = H.dist ⟨r, hrT⟩ ⟨a2, ha2T⟩
          · exact ⟨f2, hf2.1, a2, ha2, he2, fun _ _ => c2⟩
          exfalso
          have e1 : H.dist ⟨r, hrT⟩ ⟨a1, ha1T⟩ + 1 = H.dist ⟨r, hrT⟩ ⟨w, hwT⟩ := by
            generalize H.dist ⟨r, hrT⟩ ⟨a1, ha1T⟩ = D1 at *
            generalize H.dist ⟨r, hrT⟩ ⟨w, hwT⟩ = D at *
            by_cases hro : r ∈ J.outer
            · have := P1.mpr hro; have : ¬ D % 2 = 0 := fun h => Pw.mp h hro; omega
            · have : ¬ D1 % 2 = 0 := fun h => hro (P1.mp h); have := Pw.mpr hro; omega
          have e2 : H.dist ⟨r, hrT⟩ ⟨a2, ha2T⟩ + 1 = H.dist ⟨r, hrT⟩ ⟨w, hwT⟩ := by
            generalize H.dist ⟨r, hrT⟩ ⟨a2, ha2T⟩ = D2 at *
            generalize H.dist ⟨r, hrT⟩ ⟨w, hwT⟩ = D at *
            by_cases hro : r ∈ J.outer
            · have := P2.mpr hro; have : ¬ D % 2 = 0 := fun h => Pw.mp h hro; omega
            · have : ¬ D2 % 2 = 0 := fun h => hro (P2.mp h); have := Pw.mpr hro; omega
          have := hpar _ _ _ _ hadj1 hadj2 e1 e2
          have ha12 : a1 = a2 := congrArg Subtype.val this
          exact hne (hinj f1 hf1.1 f2 hf2.1 (by rw [he1, he2, ha12]))
        have hEne : Nonempty E := ⟨e⟩
        have hVne : Nonempty V := ⟨r⟩
        choose! g hgJ ag hagO hgE hgd using hchild
        have hgN : ∀ w1 ∈ J.inner, ∀ w2 ∈ J.inner, ∀ x, x ∈ G.ends (g w1) → x ∈ G.ends (g w2) → w1 = w2 := by
          intro w1 h1 w2 h2 x hx1 hx2
          rw [hgE w1 h1, Sym2.mem_iff] at hx1
          rw [hgE w2 h2, Sym2.mem_iff] at hx2
          rcases hx1 with rfl | rfl <;> rcases hx2 with h | h
          · exact h
          · exact absurd (h ▸ hagO w2 h2) (hdisj _ h1)
          · exact absurd (h ▸ hagO w1 h1) (hdisj _ h2)
          · have hw1T : w1 ∈ J.inner ∪ J.outer := Finset.mem_union_left _ h1
            have hw2T : w2 ∈ J.inner ∪ J.outer := Finset.mem_union_left _ h2
            have haT : ag w1 ∈ J.inner ∪ J.outer := Finset.mem_union_right _ (hagO w1 h1)
            have hadj1 : H.Adj ⟨w1, hw1T⟩ ⟨ag w1, haT⟩ := (hHadj _ _).mpr ⟨g w1, hgJ w1 h1, hgE w1 h1⟩
            have haT2 : ag w2 ∈ J.inner ∪ J.outer := Finset.mem_union_right _ (hagO w2 h2)
            have hadj2 : H.Adj ⟨w2, hw2T⟩ ⟨ag w2, haT2⟩ := (hHadj _ _).mpr ⟨g w2, hgJ w2 h2, hgE w2 h2⟩
            have d1 := hgd w1 h1 hw1T haT
            have d2 := hgd w2 h2 hw2T haT2
            have hsub : (⟨ag w1, haT⟩ : {x // x ∈ J.inner ∪ J.outer}) = ⟨ag w2, haT2⟩ := Subtype.ext h
            rw [← hsub] at hadj2 d2
            have := hpar _ _ _ _ hadj1 hadj2 d1 d2
            exact congrArg Subtype.val this
        have hgmem : ∀ w ∈ J.inner, w ∈ G.ends (g w) := fun w hw => by rw [hgE w hw]; exact Sym2.mem_mk_left _ _
        have hNcard : (J.inner.image g).card = J.inner.card := by
          apply Finset.card_image_of_injOn
          intro w1 h1 w2 h2 h12
          exact hgN w1 h1 w2 h2 w1 (hgmem w1 h1) (by rw [← h12]; exact hgmem w1 h1)
        have hNsub : J.inner.image g ⊆ J.edges := by
          intro f hf; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hf; exact hgJ w hw
        have hNmatch : IsMatching G (J.inner.image g) := by
          intro f1 hf1 f2 hf2 hne x hx1 hx2
          obtain ⟨w1, h1, rfl⟩ := Finset.mem_image.mp hf1
          obtain ⟨w2, h2, rfl⟩ := Finset.mem_image.mp hf2
          exact hne (by rw [hgN w1 h1 w2 h2 x hx1 hx2])
        have hcardge : J.inner.card ≤ (M ∩ J.edges).card := hNcard ▸ hmax.2.2 _ hNsub hNmatch
        have hcov : ∀ w ∈ J.inner, ∃ f ∈ M ∩ J.edges, w ∈ G.ends f := by
          intro w hw
          by_contra hcon
          push Not at hcon
          have hι : ∀ f ∈ M ∩ J.edges, ∃ i ∈ J.inner, i ∈ G.ends f := by
            intro f hf
            obtain ⟨i, hi, b, hb, h⟩ := J.edge_ends f (Finset.mem_inter.mp hf).2
            exact ⟨i, hi, by rw [h]; exact Sym2.mem_mk_left _ _⟩
          choose! ι hι1 hι2 using hι
          have := Finset.card_le_card_of_injOn (t := J.inner.erase w) ι
            (by
              intro f hf
              simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
              refine ⟨hι1 f hf, ?_⟩
              intro h; exact hcon f hf (h ▸ hι2 f hf))
            (by
              intro f1 hf1 f2 hf2 h12
              by_contra hne
              have hf1' := Finset.mem_inter.mp hf1
              have hf2' := Finset.mem_inter.mp hf2
              exact hM f1 hf1'.1 f2 hf2'.1 hne (ι f1) (hι2 f1 hf1) (h12 ▸ hι2 f2 hf2))
          rw [Finset.card_erase_of_mem hw] at this
          have : 0 < J.inner.card := Finset.card_pos.mpr ⟨w, hw⟩
          omega
        have hrO : r ∈ J.outer := by
          rcases Finset.mem_union.mp hrT with h | h
          · obtain ⟨f, hf, hrf⟩ := hcov r h
            exact absurd hrf (hrJexp f hf)
          · exact h
        have hprop : ∀ x y z f f', f ∈ J.edges → f' ∈ J.edges → G.ends f = s(x, y) → G.ends f' = s(y, z) →
            x ≠ z → x ≠ y → ((x ∈ J.outer ∧ f ∉ M) ∨ (x ∈ J.inner ∧ f ∈ M)) →
            ((y ∈ J.outer ∧ f' ∉ M) ∨ (y ∈ J.inner ∧ f' ∈ M)) := by
          intro x y z f f' hf hf' hfe hfe' hxz hxy hgood
          have hff : f ≠ f' := by
            rintro rfl
            rw [hfe, Sym2.eq_iff] at hfe'
            rcases hfe' with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact hxy h1
            · exact hxz h1
          have hyf : y ∈ G.ends f := by rw [hfe]; exact Sym2.mem_mk_right _ _
          have hyf' : y ∈ G.ends f' := by rw [hfe']; exact Sym2.mem_mk_left _ _
          rcases hgood with ⟨hxO, hfM⟩ | ⟨hxI, hfM⟩
          · have hyI : y ∈ J.inner := by
              rcases hside f hf x y hfe with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact absurd hxO (hdisj _ h1)
              · exact h2
            obtain ⟨g0, hg0, hyg0⟩ := hcov y hyI
            have hsub : ({f, f'} : Finset E) ⊆ J.edges.filter (fun e => y ∈ G.ends e) := by
              intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
              rcases hk with rfl | rfl
              · exact Finset.mem_filter.mpr ⟨hf, hyf⟩
              · exact Finset.mem_filter.mpr ⟨hf', hyf'⟩
            have heq := Finset.eq_of_subset_of_card_le hsub (by rw [J.inner_deg y hyI, Finset.card_pair hff])
            have : g0 ∈ ({f, f'} : Finset E) := by
              rw [heq]; exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hg0).2, hyg0⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl
            · exact absurd (Finset.mem_inter.mp hg0).1 hfM
            · exact Or.inr ⟨hyI, (Finset.mem_inter.mp hg0).1⟩
          · have hyO : y ∈ J.outer := by
              rcases hside f hf x y hfe with ⟨_, h2⟩ | ⟨h1, _⟩
              · exact h2
              · exact absurd h1 (hdisj _ hxI)
            refine Or.inl ⟨hyO, fun hf'M => hM f hfM f' hf'M hff y hyf hyf'⟩
        have halt : ∀ (vs : List V) (es : List E) (x : V) (f : E), IsPath G vs es →
            es.toFinset ⊆ J.edges → vs.head? = some x → es.head? = some f →
            ((x ∈ J.outer ∧ f ∉ M) ∨ (x ∈ J.inner ∧ f ∈ M)) →
            es.IsChain (fun e f => (e ∈ M ↔ f ∉ M)) ∧
              ∀ y g, vs.getLast? = some y → es.getLast? = some g → y ∈ J.outer → g ∈ M := by
          intro vs
          induction vs with
          | nil => intro es x f _ _ h; simp at h
          | cons x0 rest ih =>
            intro es x f hpath hes hhead hfh hgood
            simp only [List.head?_cons, Option.some.injEq] at hhead
            subst hhead
            cases rest with
            | nil =>
              cases es with
              | nil => simp at hfh
              | cons _ _ => exact absurd hpath.2.1 (by simp)
            | cons y rest' =>
              cases es with
              | nil => simp at hfh
              | cons f0 es' =>
                simp only [List.head?_cons, Option.some.injEq] at hfh
                subst hfh
                obtain ⟨hx, hfe, hp'⟩ := (hcons _ _ _ _ _).mp hpath
                have hf0 : f0 ∈ J.edges := hes (by simp)
                cases es' with
                | nil =>
                  have hr' : rest' = [] := by
                    have := hp'.2.1; simp at this; exact this
                  subst hr'
                  refine ⟨List.isChain_singleton _, ?_⟩
                  intro y' g hy hg hyO
                  simp at hy hg; subst hy; subst hg
                  rcases hgood with ⟨hxO, _⟩ | ⟨_, h⟩
                  · rcases hside f0 hf0 x0 _ hfe with ⟨h1, _⟩ | ⟨_, h2⟩
                    · exact absurd hxO (hdisj _ h1)
                    · exact absurd hyO (hdisj _ h2)
                  · exact h
                | cons f1 es'' =>
                  cases rest' with
                  | nil => exact absurd hp'.2.1 (by simp)
                  | cons z rest'' =>
                    obtain ⟨hy, hfe1, hp''⟩ := (hcons _ _ _ _ _).mp hp'
                    have hf1 : f1 ∈ J.edges := hes (by simp)
                    have hxz : x0 ≠ z := fun h => hx (by simp [h])
                    have hxy : x0 ≠ y := fun h => hx (by simp [h])
                    have hgood' := hprop x0 y z f0 f1 hf0 hf1 hfe hfe1 hxz hxy hgood
                    obtain ⟨ih1, ih2⟩ := ih (f1 :: es'') y f1 hp' (fun k hk => hes (by simp at hk ⊢; tauto))
                      rfl rfl hgood'
                    refine ⟨List.isChain_cons_cons.mpr ⟨?_, ih1⟩, ?_⟩
                    · rcases hside f0 hf0 x0 y hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩
                      · have n1 := hdisj _ h1; have n2 : y ∉ J.inner := fun h => hdisj _ h h2
                        rcases hgood with ⟨h3, _⟩ | ⟨_, h4⟩ <;> rcases hgood' with ⟨h5, h6⟩ | ⟨h7, h8⟩ <;> tauto
                      · have n1 : x0 ∉ J.inner := fun h => hdisj _ h h1; have n2 := hdisj _ h2
                        rcases hgood with ⟨h3, h4⟩ | ⟨h3, _⟩ <;> rcases hgood' with ⟨h5, h6⟩ | ⟨h7, h8⟩ <;> tauto
                    · intro y' g hy' hg hyO
                      rw [List.getLast?_cons_cons] at hy'
                      rw [List.getLast?_cons_cons] at hg
                      exact ih2 y' g hy' hg hyO
        have hsnoc : ∀ (vs : List V) (es : List E) (x y : V) (g : E), vs.getLast? = some x →
            (IsPath G (vs ++ [y]) (es ++ [g]) ↔ IsPath G vs es ∧ y ∉ vs ∧ G.ends g = s(x, y)) := by
          intro vs
          induction vs with
          | nil => intro es x y g h; simp at h
          | cons a rest ih =>
            intro es x y g hl
            cases rest with
            | nil =>
              simp only [List.getLast?_singleton, Option.some.injEq] at hl
              subst hl
              cases es with
              | nil =>
                simp [IsPath, eq_comm]
              | cons f es' =>
                constructor
                · intro h; have := h.2.1; simp at this
                · intro h; have := h.1.2.1; simp at this
            | cons b rest' =>
              cases es with
              | nil =>
                constructor
                · intro h; have := h.2.1; simp at this
                · intro h; have := h.1.2.1; simp at this
              | cons f es' =>
                rw [List.getLast?_cons_cons] at hl
                simp only [List.cons_append]
                rw [hcons, hcons, ← List.cons_append, ih es' x y g hl]
                simp only [List.mem_cons, List.mem_append, List.mem_singleton, not_or]
                constructor
                · rintro ⟨⟨h1, h2, _⟩, h4, h5, h6, h7⟩
                  exact ⟨⟨h1, h4, h5⟩, ⟨fun h => h2 h.symm, h6⟩, h7⟩
                · rintro ⟨⟨h1, h4, h5⟩, ⟨h2, h6⟩, h7⟩
                  exact ⟨⟨h1, fun h => h2 h.symm, by simp⟩, h4, h5, h6, h7⟩
        have huT : u ∈ J.inner ∪ J.outer := Finset.mem_union_right _ huO
        have hve : v ∈ G.ends e := by rw [he]; exact Sym2.mem_mk_right _ _
        have hvT : v ∉ J.inner ∪ J.outer := hvJ
        obtain ⟨p⟩ := hconn.preconnected ⟨r, hrT⟩ ⟨u, huT⟩
        obtain ⟨vs, es, hvsP, hvsEq, hesJ, hvsH, hvsL⟩ := hW2L _ _ p.bypass p.bypass_isPath
        simp only at hvsH hvsL
        have hvsT : vs.toFinset ⊆ J.inner ∪ J.outer := by
          intro x hx; rw [hvsEq, List.mem_toFinset, List.mem_map] at hx
          obtain ⟨w, _, rfl⟩ := hx; exact w.2
        have hvnot : v ∉ vs := fun h => hvT (hvsT (List.mem_toFinset.mpr h))
        have hPJ : PathIn G J.toSub r u vs es := ⟨hvsP, hvsT, hesJ, hvsH, hvsL⟩
        have hfullP : IsPath G (vs ++ [v]) (es ++ [e]) := (hsnoc vs es u v e hvsL).mpr ⟨hvsP, hvnot, he⟩
        have hendsP : ∀ (ws : List V) (fs : List E), IsPath G ws fs → ∀ k ∈ fs, ∀ y ∈ G.ends k, y ∈ ws := by
          intro ws
          induction ws with
          | nil => intro fs hws; have := hws.2.1; simp at this
          | cons a l ih =>
            intro fs hws k hk y hy
            cases l with
            | nil =>
              cases fs with
              | nil => simp at hk
              | cons _ _ => exact absurd hws.2.1 (by simp)
            | cons b l' =>
              cases fs with
              | nil => exact absurd hws.2.1 (by simp)
              | cons f fs' =>
                obtain ⟨_, hfe, hp⟩ := (hcons _ _ _ _ _).mp hws
                rcases List.mem_cons.mp hk with rfl | hk
                · rw [hfe, Sym2.mem_iff] at hy; rcases hy with rfl | rfl <;> simp
                · exact List.mem_cons_of_mem _ (ih fs' hp k hk y hy)
        refine ⟨vs ++ [v], es ++ [e], ⟨hfullP, ?_, ?_, ?_, ?_⟩, ?_, ⟨hfullP, ?_⟩, by simp, hrexp, hvexp⟩
        · intro x hx
          simp only [adjoinEdge, Finset.mem_insert]
          rw [List.mem_toFinset, List.mem_append] at hx
          rcases hx with hx | hx
          · exact Or.inr (Or.inr (hvsT (List.mem_toFinset.mpr hx)))
          · simp at hx; exact Or.inr (Or.inl hx)
        · intro x hx
          simp only [adjoinEdge, Finset.mem_insert]
          rw [List.mem_toFinset, List.mem_append] at hx
          rcases hx with hx | hx
          · exact Or.inr (hesJ (List.mem_toFinset.mpr hx))
          · simp at hx; exact Or.inl hx
        · cases vs with
          | nil => simp at hvsH
          | cons a l => simpa using hvsH
        · simp
        · intro ws fs hW
          obtain ⟨hwP, hwV, hwE, hwH, hwL⟩ := hW
          rcases List.eq_nil_or_concat ws with rfl | ⟨ws', w, rfl⟩
          · simp at hwH
          simp only [List.concat_eq_append] at hwP hwE hwV hwH hwL ⊢
          have hwv : w = v := by simpa using hwL
          subst hwv
          cases ws' with
          | nil =>
            simp at hwH; exact absurd (hwH ▸ hrT) hvT
          | cons a l =>
            have hwH' : a = r := by simpa using hwH
            subst hwH'
            rcases List.eq_nil_or_concat fs with rfl | ⟨fs', g, rfl⟩
            · have := hwP.2.1; simp at this
            simp only [List.concat_eq_append] at hwP hwE hwV ⊢
            obtain ⟨x, hx⟩ : ∃ x, (a :: l).getLast? = some x := ⟨_, List.getLast?_eq_getLast_of_ne_nil (by simp)⟩
            obtain ⟨hP', hvn', hge'⟩ := (hsnoc (a :: l) fs' x w g hx).mp hwP
            have hgE : g ∈ insert e J.edges := hwE (by simp)
            have hwg : w ∈ G.ends g := by rw [hge']; exact Sym2.mem_mk_right _ _
            have hge : g = e := by
              rcases Finset.mem_insert.mp hgE with h | h
              · exact h
              · exact absurd (hmemT g h w hwg) hvT
            subst hge
            have hxu : x = u := by
              rw [he, Sym2.eq_iff] at hge'
              rcases hge' with ⟨h1, _⟩ | ⟨h1, h2⟩
              · exact h1.symm
              · exact absurd (h1 ▸ huT) hvT
            subst hxu
            have hT' : (a :: l).toFinset ⊆ J.inner ∪ J.outer := by
              intro y hy
              have h1 := hwV (by simp at hy ⊢; tauto)
              simp only [adjoinEdge, Finset.mem_insert] at h1
              rcases h1 with h1 | h1 | h1
              · rw [h1]; exact huT
              · exact absurd (h1 ▸ List.mem_toFinset.mp hy) hvn'
              · exact h1
            have hE' : fs'.toFinset ⊆ J.edges := by
              intro k hk
              have h1 := hwE (by simp at hk ⊢; tauto)
              simp only [adjoinEdge, Finset.mem_insert] at h1
              rcases h1 with h1 | h1
              · subst h1; exact absurd (hendsP _ _ hP' k (List.mem_toFinset.mp hk) _ hve) hvn'
              · exact h1
            obtain ⟨h1, h2⟩ := huniqJ a x (a :: l) fs' vs es ⟨hP', hT', hE', rfl, hx⟩ hPJ
            exact ⟨by rw [h1], by rw [h2]⟩

        · rw [List.isChain_append]
          rcases es with _ | ⟨f0, es'⟩
          · simp
          · cases vs with
            | nil => simp at hvsH
            | cons x0 vs' =>
              cases vs' with
              | nil => exact absurd hvsP.2.1 (by simp)
              | cons y vs'' =>
                have hx0 : x0 = r := by simpa using hvsH
                subst hx0
                obtain ⟨_, hfe0, _⟩ := (hcons _ _ _ _ _).mp hvsP
                have hgood : (x0 ∈ J.outer ∧ f0 ∉ M) ∨ (x0 ∈ J.inner ∧ f0 ∈ M) :=
                  Or.inl ⟨hrO, fun h => hrexp f0 h (by rw [hfe0]; exact Sym2.mem_mk_left _ _)⟩
                obtain ⟨c1, c2⟩ := halt _ _ x0 f0 hvsP hesJ hvsH rfl hgood
                refine ⟨c1, List.isChain_singleton _, ?_⟩
                intro g hg k hk
                simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hk
                subst hk
                have hgM := c2 u g hvsL hg huO
                exact ⟨fun _ hk => hvexp _ hk hve, fun _ => hgM⟩
