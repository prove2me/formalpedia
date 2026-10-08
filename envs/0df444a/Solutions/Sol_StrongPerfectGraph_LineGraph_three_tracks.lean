-- Prove2me | solution 1 for StrongPerfectGraph.LineGraph.three_tracks
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:08:44.913345+00:00
-- url     : https://prove2.me/submissions/59237fcd-0390-47f6-abcd-b4e26bee5e5a

/-
Three tracks through prescribed edges in a 3-connected graph (CRST 7.1).

Let c₁c₂ be an edge of a 3-connected graph J and x, y two further neighbours of c₁. Apply Menger's
theorem (proved below, set form) in J minus {c₁, c₂} to A = {x, y} and B = N(c₂) ∖ {c₁}: every
A–B separator has at least two vertices by 3-connectivity (a single vertex z together with c₁ would
be a 2-vertex cut of J), so there are two disjoint A–B paths, one starting at x and one at y.
Prefix c₁ and append c₂ to obtain the two tracks; the edge c₁c₂ is the third.
-/
import Mathlib
import Definitions.Def_StrongPerfectGraph_LineGraph_IsSubdivision

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SPGTLib.Menger

variable {V : Type*} [DecidableEq V]

/-- A path of `G` inside the vertex set `S`, listed from a vertex of `A` to a vertex of `B`. -/
def IsABPath (G : SimpleGraph V) (S A B : Finset V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ List.IsChain G.Adj p ∧ (∀ v ∈ p, v ∈ S) ∧
    (∃ a, p.head? = some a ∧ a ∈ A) ∧ (∃ b, p.getLast? = some b ∧ b ∈ B)

/-- `X` meets every `A`–`B` path of `G` inside `S`. -/
def IsABSep (G : SimpleGraph V) (S A B X : Finset V) : Prop :=
  ∀ p, IsABPath G S A B p → ∃ x ∈ X, x ∈ p

/-- `k` pairwise vertex-disjoint `A`–`B` paths of `G` inside `S`. -/
def HasLinkage (G : SimpleGraph V) (S A B : Finset V) (k : ℕ) : Prop :=
  ∃ L : List (List V), L.length = k ∧ (∀ p ∈ L, IsABPath G S A B p) ∧
    L.Pairwise (fun p q => ∀ v ∈ p, v ∉ q)

section basics

variable {G G' : SimpleGraph V} {S S' A A' B B' X : Finset V} {p : List V}

theorem IsABPath.mono_graph (h : IsABPath G S A B p) (hG : G ≤ G') : IsABPath G' S A B p :=
  ⟨h.1, h.2.1, h.2.2.1.imp (fun _ _ hab => hG hab), h.2.2.2.1, h.2.2.2.2⟩

theorem IsABPath.mono (h : IsABPath G S A B p) (hS : S ⊆ S') (hA : A ⊆ A') (hB : B ⊆ B') :
    IsABPath G S' A' B' p := by
  obtain ⟨hne, hnd, hch, hSp, ⟨a, ha, haA⟩, ⟨b, hb, hbB⟩⟩ := h
  exact ⟨hne, hnd, hch, fun v hv => hS (hSp v hv), ⟨a, ha, hA haA⟩, ⟨b, hb, hB hbB⟩⟩

theorem IsABPath.reverse (h : IsABPath G S A B p) : IsABPath G S B A p.reverse := by
  obtain ⟨hne, hnd, hch, hSp, ⟨a, ha, haA⟩, ⟨b, hb, hbB⟩⟩ := h
  refine ⟨by simpa using hne, List.nodup_reverse.mpr hnd, ?_,
    fun v hv => hSp v (List.mem_reverse.mp hv),
    ⟨b, by simpa [List.head?_reverse] using hb, hbB⟩,
    ⟨a, by simpa [List.getLast?_reverse] using ha, haA⟩⟩
  rw [List.isChain_reverse]
  exact hch.imp (fun u w h => h.symm)

theorem IsABSep.symm (h : IsABSep G S A B X) : IsABSep G S B A X := by
  intro p hp
  obtain ⟨x, hx, hxp⟩ := h p.reverse hp.reverse
  exact ⟨x, hx, List.mem_reverse.mp hxp⟩

end basics

/-- Two members of a pairwise-disjoint family that share a vertex coincide. -/
theorem eq_of_mem_of_mem {L : List (List V)} (hL : L.Pairwise (fun p q => ∀ v ∈ p, v ∉ q))
    {p q : List V} (hp : p ∈ L) (hq : q ∈ L) {v : V} (hvp : v ∈ p) (hvq : v ∈ q) : p = q := by
  induction L with
  | nil => exact absurd hp (by simp)
  | cons a t ih =>
    rw [List.pairwise_cons] at hL
    obtain ⟨h1, h2⟩ := hL
    rcases List.mem_cons.mp hp with rfl | hpt <;> rcases List.mem_cons.mp hq with rfl | hqt
    · rfl
    · exact absurd hvq (h1 q hqt v hvp)
    · exact absurd hvp (h1 p hpt v hvq)
    · exact ih h2 hpt hqt

/-- A full-size family of disjoint paths ending in `X` ends in every vertex of `X` exactly once,
and meets `X` only at its last vertices. -/
theorem linkage_ends {G : SimpleGraph V} {S A X : Finset V} (L : List (List V))
    (hlen : L.length = X.card) (hL : ∀ p ∈ L, IsABPath G S A X p)
    (hpw : L.Pairwise (fun p q => ∀ v ∈ p, v ∉ q)) :
    (∀ x ∈ X, ∃ p ∈ L, p.getLast? = some x) ∧
      (∀ p ∈ L, ∀ v ∈ p, v ∈ X → p.getLast? = some v) := by
  by_cases hX : X = ∅
  · subst hX
    have : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst this
    simp
  obtain ⟨x0, hx0⟩ := Finset.nonempty_iff_ne_empty.mpr hX
  let f : List V → V := fun p => (p.getLast?).getD x0
  have hf : ∀ p ∈ L, p.getLast? = some (f p) ∧ f p ∈ X := by
    intro p hp
    obtain ⟨b, hb, hbX⟩ := (hL p hp).2.2.2.2.2
    simp [f, hb, hbX]
  have hfmem : ∀ p ∈ L, f p ∈ p := fun p hp => List.mem_of_getLast? (hf p hp).1
  have hnd : (L.map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hpw.imp_of_mem ?_
    intro p q hp hq hdisj heq
    exact hdisj (f p) (hfmem p hp) (heq ▸ hfmem q hq)
  have hsub : (L.map f).toFinset ⊆ X := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    exact (hf p hp).2
  have hcard : (L.map f).toFinset.card = X.card := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hlen]
  have heq : (L.map f).toFinset = X := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨fun x hx => ?_, fun p hp v hvp hvX => ?_⟩
  · rw [← heq] at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact ⟨p, hp, (hf p hp).1⟩
  · rw [← heq] at hvX
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hvX)
    have hpq := eq_of_mem_of_mem hpw hp hq hvp (hfmem q hq)
    subst hpq
    exact (hf p hp).1

/-- Gluing an `A`–`X` linkage and a `B`–`X` linkage that meet only in `X`. -/
theorem combine {G : SimpleGraph V} {S SA SB A B X : Finset V}
    (hSA : SA ⊆ S) (hSB : SB ⊆ S) (hint : ∀ v, v ∈ SA → v ∈ SB → v ∈ X)
    (LA : List (List V)) (hLAlen : LA.length = X.card)
    (hLA : ∀ p ∈ LA, IsABPath G SA A X p) (hLApw : LA.Pairwise (fun p q => ∀ v ∈ p, v ∉ q))
    (LB : List (List V)) (hLBlen : LB.length = X.card)
    (hLB : ∀ p ∈ LB, IsABPath G SB B X p) (hLBpw : LB.Pairwise (fun p q => ∀ v ∈ p, v ∉ q)) :
    HasLinkage G S A B X.card := by
  obtain ⟨hA1, hA2⟩ := linkage_ends LA hLAlen hLA hLApw
  obtain ⟨hB1, hB2⟩ := linkage_ends LB hLBlen hLB hLBpw
  choose! pA hpA using hA1
  choose! pB hpB using hB1
  have hrev : ∀ x ∈ X, ∃ r, (pB x).reverse = x :: r := by
    intro x hx
    obtain ⟨hmem, hlast⟩ := hpB x hx
    have hne : (pB x).reverse ≠ [] := by simpa using (hLB _ hmem).1
    have hhead : (pB x).reverse.head? = some x := by rw [List.head?_reverse]; exact hlast
    cases hh : (pB x).reverse with
    | nil => exact absurd hh hne
    | cons a t =>
      rw [hh] at hhead
      simp at hhead
      exact ⟨t, by rw [hhead]⟩
  choose! r hr using hrev
  have hfact : ∀ x ∈ X,
      IsABPath G SA A X (pA x) ∧ (pA x).getLast? = some x ∧ (∀ v ∈ pA x, v ∈ X → v = x) ∧
      (∀ v ∈ r x, v ∈ SB ∧ v ∉ X) ∧ List.IsChain G.Adj (x :: r x) ∧ (x :: r x).Nodup ∧
      (∃ b, (x :: r x).getLast? = some b ∧ b ∈ B) := by
    intro x hx
    obtain ⟨hmem, hlast⟩ := hpA x hx
    obtain ⟨hmemB, hlastB⟩ := hpB x hx
    have hpath := hLB _ hmemB
    have hrx := hr x hx
    refine ⟨hLA _ hmem, hlast, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv hvX
      have := hA2 _ hmem v hv hvX
      rw [hlast] at this
      exact (Option.some.inj this).symm
    · intro v hv
      have hvB : v ∈ pB x := List.mem_reverse.mp (by rw [hrx]; exact List.mem_cons_of_mem _ hv)
      refine ⟨hpath.2.2.2.1 v hvB, fun hvX => ?_⟩
      have := hB2 _ hmemB v hvB hvX
      rw [hlastB] at this
      have hvx : v = x := (Option.some.inj this).symm
      have hnd : (x :: r x).Nodup := by rw [← hrx]; exact List.nodup_reverse.mpr hpath.2.1
      rw [List.nodup_cons] at hnd
      exact hnd.1 (hvx ▸ hv)
    · rw [← hrx, List.isChain_reverse]
      exact hpath.2.2.1.imp (fun a b h => h.symm)
    · rw [← hrx]; exact List.nodup_reverse.mpr hpath.2.1
    · obtain ⟨b, hb, hbB⟩ := hpath.2.2.2.2.1
      exact ⟨b, by rw [← hrx, List.getLast?_reverse]; exact hb, hbB⟩
  refine ⟨X.toList.map (fun x => pA x ++ r x), by simp, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, hxl, rfl⟩ := List.mem_map.mp hp
    have hx : x ∈ X := Finset.mem_toList.mp hxl
    obtain ⟨hpath, hlast, honly, hrest, hch, hnd, hbend⟩ := hfact x hx
    have hdisj : ∀ v ∈ pA x, v ∉ r x := by
      intro v hv hvr
      have hvA := hpath.2.2.2.1 v hv
      obtain ⟨hvB, hvX⟩ := hrest v hvr
      exact hvX (hint v hvA hvB)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact hpath.1 (List.append_eq_nil_iff.mp h).1
    · rw [List.nodup_append]
      exact ⟨hpath.2.1, (List.nodup_cons.mp hnd).2, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
    · rw [List.isChain_append]
      refine ⟨hpath.2.2.1, (List.isChain_cons.mp hch).2, ?_⟩
      intro u hu w hw
      rw [hlast] at hu
      have hux : x = u := Option.some.inj hu
      subst hux
      exact (List.isChain_cons.mp hch).1 w hw
    · intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact hSA (hpath.2.2.2.1 v h)
      · exact hSB (hrest v h).1
    · obtain ⟨a, ha, haA⟩ := hpath.2.2.2.2.1
      refine ⟨a, ?_, haA⟩
      rw [List.head?_append_of_ne_nil _ hpath.1]; exact ha
    · obtain ⟨b, hb, hbB⟩ := hbend
      refine ⟨b, ?_, hbB⟩
      rcases hrr : r x with _ | ⟨y, t⟩
      · rw [hrr] at hb
        simp at hb
        subst hb
        simpa using hlast
      · rw [hrr] at hb
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        simpa [List.getLast?_cons] using hb
  · rw [List.pairwise_map]
    refine (show X.toList.Pairwise (· ≠ ·) from Finset.nodup_toList X).imp_of_mem ?_
    intro x y hxl hyl hxy v hvx hvy
    have hx : x ∈ X := Finset.mem_toList.mp hxl
    have hy : y ∈ X := Finset.mem_toList.mp hyl
    obtain ⟨hpathx, hlastx, honlyx, hrestx, _, _, _⟩ := hfact x hx
    obtain ⟨hpathy, hlasty, honlyy, hresty, _, _, _⟩ := hfact y hy
    rcases List.mem_append.mp hvx with h1 | h1 <;> rcases List.mem_append.mp hvy with h2 | h2
    · have := eq_of_mem_of_mem hLApw (hpA x hx).1 (hpA y hy).1 h1 h2
      rw [this] at hlastx
      rw [hlastx] at hlasty
      exact hxy (Option.some.inj hlasty)
    · exact (hresty v h2).2 (hint v (hpathx.2.2.2.1 v h1) (hresty v h2).1)
    · exact (hrestx v h1).2 (hint v (hpathy.2.2.2.1 v h2) (hrestx v h1).1)
    · have hv1 : v ∈ pB x := List.mem_reverse.mp (by rw [hr x hx]; exact List.mem_cons_of_mem _ h1)
      have hv2 : v ∈ pB y := List.mem_reverse.mp (by rw [hr y hy]; exact List.mem_cons_of_mem _ h2)
      have := eq_of_mem_of_mem hLBpw (hpB x hx).1 (hpB y hy).1 hv1 hv2
      have h3 := (hpB x hx).2
      have h4 := (hpB y hy).2
      rw [this] at h3
      rw [h3] at h4
      exact hxy (Option.some.inj h4)

/-- The subgraph of `G` induced on `T`, as a graph on the same vertex type. -/
def Hgraph (G : SimpleGraph V) (T : Finset V) : SimpleGraph V where
  Adj u w := G.Adj u w ∧ u ∈ T ∧ w ∈ T
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

open Classical in
/-- Vertices of `T` reachable inside `T` from a vertex of `A ∩ T`. -/
noncomputable def reachSet (G : SimpleGraph V) (T A : Finset V) : Finset V :=
  T.filter (fun v => ∃ a ∈ A, a ∈ T ∧ (Hgraph G T).Reachable a v)

theorem mem_reachSet {G : SimpleGraph V} {T A : Finset V} {v : V} :
    v ∈ reachSet G T A ↔ v ∈ T ∧ ∃ a ∈ A, a ∈ T ∧ (Hgraph G T).Reachable a v := by
  unfold reachSet
  simp

theorem walk_support_mem {G : SimpleGraph V} {T : Finset V} {a b : V}
    (w : (Hgraph G T).Walk a b) (ha : a ∈ T) : ∀ v ∈ w.support, v ∈ T := by
  induction w with
  | nil => intro v hv; simp at hv; exact hv ▸ ha
  | cons h w ih =>
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ha
    · exact ih h.2.2 v hv

theorem reach_mem {G : SimpleGraph V} {T : Finset V} {a b : V}
    (h : (Hgraph G T).Reachable a b) (ha : a ∈ T) : b ∈ T := by
  obtain ⟨w⟩ := h
  exact walk_support_mem w ha b w.end_mem_support

theorem reach_of_chain {G : SimpleGraph V} {T : Finset V} :
    ∀ (p : List V) (a : V), p.head? = some a → List.IsChain G.Adj p → (∀ v ∈ p, v ∈ T) →
      ∀ v ∈ p, (Hgraph G T).Reachable a v := by
  intro p
  induction p with
  | nil => intro a h; simp at h
  | cons b t ih =>
    intro a ha hch hT v hv
    have hab : b = a := by simpa using ha
    subst hab
    rcases List.mem_cons.mp hv with rfl | hvt
    · exact SimpleGraph.Reachable.refl _
    · cases t with
      | nil => exact absurd hvt (by simp)
      | cons c t' =>
        have hadj : G.Adj b c := (List.isChain_cons_cons.mp hch).1
        have hH : (Hgraph G T).Adj b c := ⟨hadj, hT b (by simp), hT c (by simp)⟩
        have := ih c rfl (List.isChain_cons_cons.mp hch).2
          (fun w hw => hT w (List.mem_cons_of_mem _ hw)) v hvt
        exact hH.reachable.trans this

theorem exists_path_of_reach {G : SimpleGraph V} {T : Finset V} {a b : V} (ha : a ∈ T)
    (h : (Hgraph G T).Reachable a b) : ∃ p, IsABPath G T {a} {b} p := by
  obtain ⟨w⟩ := h
  let P := w.toPath
  refine ⟨P.1.support, P.1.support_ne_nil, P.2.support_nodup, ?_, ?_, ⟨a, ?_, by simp⟩,
    ⟨b, ?_, by simp⟩⟩
  · exact P.1.isChain_adj_support.imp (fun u v huv => huv.1)
  · exact walk_support_mem P.1 ha
  · rw [← SimpleGraph.Walk.cons_tail_support P.1]; rfl
  · rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil P.1),
      SimpleGraph.Walk.getLast_support]

theorem firstX_prefix {G : SimpleGraph V} {S X : Finset V} (a0 : V) :
    ∀ (p : List V) (c : V), p.head? = some c → List.IsChain G.Adj p → (∀ v ∈ p, v ∈ S) →
      (c ∈ X ∨ (a0 ∈ S \ X ∧ (Hgraph G (S \ X)).Reachable a0 c)) → (∃ x ∈ X, x ∈ p) →
      ∃ q, q <+: p ∧ q.head? = some c ∧ (∃ x ∈ X, q.getLast? = some x) ∧
        ∀ v ∈ q, v ∈ X ∨ (a0 ∈ S \ X ∧ (Hgraph G (S \ X)).Reachable a0 v) := by
  intro p
  induction p with
  | nil => intro c h; simp at h
  | cons b t ih =>
    intro c hc hch hS hcase ⟨x, hxX, hxp⟩
    have hbc : b = c := by simpa using hc
    subst hbc
    by_cases hbX : b ∈ X
    · refine ⟨[b], ⟨t, rfl⟩, rfl, ⟨b, hbX, rfl⟩, ?_⟩
      intro v hv
      simp at hv
      exact Or.inl (hv ▸ hbX)
    · have hcase' : a0 ∈ S \ X ∧ (Hgraph G (S \ X)).Reachable a0 b := by
        rcases hcase with h | h
        · exact absurd h hbX
        · exact h
      have hxt : x ∈ t := by
        rcases List.mem_cons.mp hxp with rfl | h
        · exact absurd hxX hbX
        · exact h
      cases t with
      | nil => exact absurd hxt (by simp)
      | cons d t' =>
        have hadj : G.Adj b d := (List.isChain_cons_cons.mp hch).1
        have hbS : b ∈ S \ X := Finset.mem_sdiff.mpr ⟨hS b (by simp), hbX⟩
        have hdS : d ∈ S := hS d (by simp)
        have hdcase : d ∈ X ∨ (a0 ∈ S \ X ∧ (Hgraph G (S \ X)).Reachable a0 d) := by
          by_cases hdX : d ∈ X
          · exact Or.inl hdX
          · exact Or.inr ⟨hcase'.1, hcase'.2.trans
              (SimpleGraph.Adj.reachable (show (Hgraph G (S \ X)).Adj b d from
                ⟨hadj, hbS, Finset.mem_sdiff.mpr ⟨hdS, hdX⟩⟩))⟩
        obtain ⟨q', hq'p, hq'h, ⟨x', hx'X, hx'⟩, hq'v⟩ := ih d rfl
          (List.isChain_cons_cons.mp hch).2 (fun w hw => hS w (List.mem_cons_of_mem _ hw))
          hdcase ⟨x, hxX, hxt⟩
        obtain ⟨u, hu⟩ := hq'p
        refine ⟨b :: q', ⟨u, by simp [hu]⟩, rfl, ⟨x', hx'X, ?_⟩, ?_⟩
        · cases q' with
          | nil => simp at hq'h
          | cons e q'' => simpa [List.getLast?_cons_cons] using hx'
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact Or.inr hcase'
          · exact hq'v v hv

/-- A separator of the `A`–`X` subproblem separates `A` from `B` in the whole graph. -/
theorem sep_restrict {G : SimpleGraph V} {S A B X X'' : Finset V} (hX : IsABSep G S A B X)
    (h'' : IsABSep G (reachSet G (S \ X) A ∪ X) A X X'') : IsABSep G S A B X'' := by
  intro p hp
  have hp' := hp
  obtain ⟨hne, hnd, hch, hSp, ⟨a0, ha0, ha0A⟩, ⟨b, hb, hbB⟩⟩ := hp'
  obtain ⟨x, hxX, hxp⟩ := hX p hp
  have ha0S : a0 ∈ S := hSp a0 (List.mem_of_mem_head? ha0)
  have hcase : a0 ∈ X ∨ (a0 ∈ S \ X ∧ (Hgraph G (S \ X)).Reachable a0 a0) := by
    by_cases h : a0 ∈ X
    · exact Or.inl h
    · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨ha0S, h⟩, SimpleGraph.Reachable.refl _⟩
  obtain ⟨q, hqp, hqh, ⟨x', hx'X, hx'⟩, hqv⟩ :=
    firstX_prefix a0 p a0 ha0 hch hSp hcase ⟨x, hxX, hxp⟩
  have hqpath : IsABPath G (reachSet G (S \ X) A ∪ X) A X q := by
    obtain ⟨u, hu⟩ := hqp
    refine ⟨?_, ?_, ?_, ?_, ⟨a0, hqh, ha0A⟩, ⟨x', hx', hx'X⟩⟩
    · intro h; subst h; simp at hqh
    · rw [← hu] at hnd; exact (List.nodup_append.mp hnd).1
    · rw [← hu] at hch; exact (List.isChain_append.mp hch).1
    · intro v hv
      rcases hqv v hv with h | ⟨ha0T, hr⟩
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (mem_reachSet.mpr
          ⟨reach_mem hr ha0T, a0, ha0A, ha0T, hr⟩)
  obtain ⟨y, hy, hyq⟩ := h'' q hqpath
  exact ⟨y, hy, hqp.subset hyq⟩

open Classical in
/-- Number of ordered adjacent pairs inside `S` (the measure for the induction). -/
noncomputable def edgeCount (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((S ×ˢ S).filter (fun x => G.Adj x.1 x.2)).card

theorem edgeCount_mono {G : SimpleGraph V} {S S' : Finset V} (h : S ⊆ S') :
    edgeCount G S ≤ edgeCount G S' := by
  classical
  unfold edgeCount
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_product] at hx ⊢
  exact ⟨⟨h hx.1.1, h hx.1.2⟩, hx.2⟩

theorem edgeCount_delete_lt {G : SimpleGraph V} {S : Finset V} {u w : V} (hadj : G.Adj u w)
    (hu : u ∈ S) (hw : w ∈ S) : edgeCount (G.deleteEdges {s(u, w)}) S < edgeCount G S := by
  classical
  unfold edgeCount
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, SimpleGraph.deleteEdges_adj] at hx ⊢
    exact ⟨hx.1, hx.2.1⟩
  · intro hsub
    have := hsub (show (u, w) ∈ (S ×ˢ S).filter (fun x => G.Adj x.1 x.2) by
      simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hu, hw⟩, hadj⟩)
    simp only [Finset.mem_filter, Finset.mem_product, SimpleGraph.deleteEdges_adj] at this
    exact this.2.2 (by simp)

theorem chain_delete {G : SimpleGraph V} {u w : V} :
    ∀ q : List V, List.IsChain G.Adj q → ¬ (u ∈ q ∧ w ∈ q) →
      List.IsChain (G.deleteEdges {s(u, w)}).Adj q := by
  intro q
  induction q with
  | nil => intro _ _; exact List.isChain_nil
  | cons a t ih =>
    intro hch hnot
    cases t with
    | nil => exact List.isChain_singleton _
    | cons b t' =>
      obtain ⟨hab, hrest⟩ := List.isChain_cons_cons.mp hch
      refine List.isChain_cons_cons.mpr ⟨?_, ih hrest (fun h => hnot ⟨List.mem_cons_of_mem _ h.1, List.mem_cons_of_mem _ h.2⟩)⟩
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hab, ?_⟩
      intro hmem
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
      apply hnot
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩

theorem no_AB_path_in_T {G : SimpleGraph V} {S A B X : Finset V} (hX : IsABSep G S A B X)
    (hXS : X ⊆ S) {a b : V} (ha : a ∈ A) (hb : b ∈ B) (haT : a ∈ S \ X)
    (hr : (Hgraph G (S \ X)).Reachable a b) : False := by
  obtain ⟨p, hp⟩ := exists_path_of_reach haT hr
  have hp' : IsABPath G S A B p := hp.mono Finset.sdiff_subset (by simpa using ha) (by simpa using hb)
  obtain ⟨x, hxX, hxp⟩ := hX p hp'
  have hxT : x ∈ S \ X := hp.2.2.2.1 x hxp
  exact (Finset.mem_sdiff.mp hxT).2 hxX

theorem sep_of_whole {G : SimpleGraph V} {S A B : Finset V} : IsABSep G S A B B := by
  intro p hp
  obtain ⟨b, hb, hbB⟩ := hp.2.2.2.2.2
  exact ⟨b, hbB, List.mem_of_getLast? hb⟩

theorem sep_of_whole' {G : SimpleGraph V} {S A B : Finset V} : IsABSep G S A B A := by
  intro p hp
  obtain ⟨a, ha, haA⟩ := hp.2.2.2.2.1
  exact ⟨a, haA, List.mem_of_mem_head? ha⟩

/-- The splitting case of Menger's theorem: a minimum separator `X` different from `A` and `B`. -/
theorem case_split (G : SimpleGraph V) (S A B X : Finset V) (k n : ℕ)
    (hμ : S.card + edgeCount G S ≤ n + 1) (hA : A ⊆ S) (hB : B ⊆ S)
    (hsep : ∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card)
    (hXS : X ⊆ S) (hXsep : IsABSep G S A B X) (hXk : X.card = k) (hXA : X ≠ A) (hXB : X ≠ B)
    (ih : ∀ (G : SimpleGraph V) (S A B : Finset V) (k : ℕ),
      S.card + edgeCount G S ≤ n → A ⊆ S → B ⊆ S →
      (∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) → HasLinkage G S A B k) :
    HasLinkage G S A B k := by
  classical
  have hBnX : ¬ B ⊆ X := by
    intro hBX
    have h1 := hsep B hB sep_of_whole
    exact hXB (Finset.eq_of_subset_of_card_le hBX (by omega)).symm
  have hAnX : ¬ A ⊆ X := by
    intro hAX
    have h1 := hsep A hA sep_of_whole'
    exact hXA (Finset.eq_of_subset_of_card_le hAX (by omega)).symm
  obtain ⟨b, hbB, hbX⟩ := Finset.not_subset.mp hBnX
  obtain ⟨a, haA, haX⟩ := Finset.not_subset.mp hAnX
  set T := S \ X with hT
  set VA := reachSet G T A with hVA
  set VB := reachSet G T B with hVB
  set SA := VA ∪ X with hSAdef
  set SB := VB ∪ X with hSBdef
  have hVAT : VA ⊆ T := fun v hv => (mem_reachSet.mp hv).1
  have hVBT : VB ⊆ T := fun v hv => (mem_reachSet.mp hv).1
  have hSAS : SA ⊆ S := Finset.union_subset (hVAT.trans Finset.sdiff_subset) hXS
  have hSBS : SB ⊆ S := Finset.union_subset (hVBT.trans Finset.sdiff_subset) hXS
  have hASA : A ⊆ SA := by
    intro v hv
    by_cases hvX : v ∈ X
    · exact Finset.mem_union_right _ hvX
    · exact Finset.mem_union_left _ (mem_reachSet.mpr ⟨Finset.mem_sdiff.mpr ⟨hA hv, hvX⟩, v, hv,
        Finset.mem_sdiff.mpr ⟨hA hv, hvX⟩, SimpleGraph.Reachable.refl _⟩)
  have hBSB : B ⊆ SB := by
    intro v hv
    by_cases hvX : v ∈ X
    · exact Finset.mem_union_right _ hvX
    · exact Finset.mem_union_left _ (mem_reachSet.mpr ⟨Finset.mem_sdiff.mpr ⟨hB hv, hvX⟩, v, hv,
        Finset.mem_sdiff.mpr ⟨hB hv, hvX⟩, SimpleGraph.Reachable.refl _⟩)
  have hXSA : X ⊆ SA := Finset.subset_union_right
  have hXSB : X ⊆ SB := Finset.subset_union_right
  have hbT : b ∈ T := Finset.mem_sdiff.mpr ⟨hB hbB, hbX⟩
  have haT : a ∈ T := Finset.mem_sdiff.mpr ⟨hA haA, haX⟩
  have hbSA : b ∉ SA := by
    intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨_, a', ha', ha'T, hr⟩ := mem_reachSet.mp hb
      exact no_AB_path_in_T hXsep hXS ha' hbB ha'T hr
    · exact hbX hb
  have haSB : a ∉ SB := by
    intro ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨_, b', hb', hb'T, hr⟩ := mem_reachSet.mp ha
      exact no_AB_path_in_T hXsep hXS haA hb' haT hr.symm
    · exact haX ha
  have hVAVB : ∀ v, v ∈ VA → v ∈ VB → False := by
    intro v hvA hvB
    obtain ⟨_, a', ha', ha'T, hra⟩ := mem_reachSet.mp hvA
    obtain ⟨_, b', hb', hb'T, hrb⟩ := mem_reachSet.mp hvB
    exact no_AB_path_in_T hXsep hXS ha' hb' ha'T (hra.trans hrb.symm)
  have hint : ∀ v, v ∈ SA → v ∈ SB → v ∈ X := by
    intro v hvA hvB
    rcases Finset.mem_union.mp hvA with h1 | h1
    · rcases Finset.mem_union.mp hvB with h2 | h2
      · exact absurd (hVAVB v h1 h2) id
      · exact h2
    · exact h1
  have hSAlt : SA.card < S.card := Finset.card_lt_card ⟨hSAS, fun h => hbSA (h (hB hbB))⟩
  have hSBlt : SB.card < S.card := Finset.card_lt_card ⟨hSBS, fun h => haSB (h (hA haA))⟩
  have hμA : SA.card + edgeCount G SA ≤ n := by
    have := edgeCount_mono (G := G) hSAS
    omega
  have hμB : SB.card + edgeCount G SB ≤ n := by
    have := edgeCount_mono (G := G) hSBS
    omega
  have hsepA : ∀ X'', X'' ⊆ SA → IsABSep G SA A X X'' → k ≤ X''.card :=
    fun X'' hX'' hsp => hsep X'' (hX''.trans hSAS) (sep_restrict hXsep hsp)
  have hsepB : ∀ X'', X'' ⊆ SB → IsABSep G SB B X X'' → k ≤ X''.card :=
    fun X'' hX'' hsp => hsep X'' (hX''.trans hSBS) (sep_restrict hXsep.symm hsp).symm
  obtain ⟨LA, hLAlen, hLA, hLApw⟩ := ih G SA A X k hμA hASA hXSA hsepA
  obtain ⟨LB, hLBlen, hLB, hLBpw⟩ := ih G SB B X k hμB hBSB hXSB hsepB
  have := combine hSAS hSBS hint LA (by omega) hLA hLApw LB (by omega) hLB hLBpw
  rwa [hXk] at this

/-- A vertex lying in `A ∩ B` is a trivial path; remove it and induct. -/
theorem case_common (G : SimpleGraph V) (S A B : Finset V) (k n : ℕ)
    (hμ : S.card + edgeCount G S ≤ n + 1) (hA : A ⊆ S) (hB : B ⊆ S)
    (hsep : ∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) (x : V) (hxA : x ∈ A) (hxB : x ∈ B)
    (ih : ∀ (G : SimpleGraph V) (S A B : Finset V) (k : ℕ),
      S.card + edgeCount G S ≤ n → A ⊆ S → B ⊆ S →
      (∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) → HasLinkage G S A B k) :
    HasLinkage G S A B k := by
  classical
  have hxS : x ∈ S := hA hxA
  by_cases hk : k = 0
  · subst hk; exact ⟨[], rfl, by simp, List.Pairwise.nil⟩
  have hcard : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hxS
  have hμ' : (S.erase x).card + edgeCount G (S.erase x) ≤ n := by
    have := edgeCount_mono (G := G) (Finset.erase_subset x S)
    omega
  have hsep' : ∀ X', X' ⊆ S.erase x → IsABSep G (S.erase x) (A.erase x) (B.erase x) X' →
      k - 1 ≤ X'.card := by
    intro X' hX'S hsp
    have hsp2 : IsABSep G S A B (insert x X') := by
      intro q hq
      by_cases hxq : x ∈ q
      · exact ⟨x, Finset.mem_insert_self _ _, hxq⟩
      · obtain ⟨hne, hnd, hch, hSq, ⟨a, ha, haA⟩, ⟨b, hb, hbB⟩⟩ := hq
        have hq' : IsABPath G (S.erase x) (A.erase x) (B.erase x) q := by
          refine ⟨hne, hnd, hch, ?_, ⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩⟩
          · intro v hv
            exact Finset.mem_erase.mpr ⟨fun h => hxq (h ▸ hv), hSq v hv⟩
          · exact Finset.mem_erase.mpr ⟨fun h => hxq (h ▸ List.mem_of_mem_head? ha), haA⟩
          · exact Finset.mem_erase.mpr ⟨fun h => hxq (h ▸ List.mem_of_getLast? hb), hbB⟩
        obtain ⟨y, hy, hyq⟩ := hsp q hq'
        exact ⟨y, Finset.mem_insert_of_mem hy, hyq⟩
    have hsub : insert x X' ⊆ S :=
      Finset.insert_subset hxS (hX'S.trans (Finset.erase_subset x S))
    have h1 := hsep _ hsub hsp2
    have h2 := Finset.card_insert_le x X'
    omega
  obtain ⟨L, hL1, hL2, hL3⟩ := ih G (S.erase x) (A.erase x) (B.erase x) (k - 1) hμ'
    (Finset.erase_subset_erase x hA) (Finset.erase_subset_erase x hB) hsep'
  refine ⟨[x] :: L, by simp [hL1]; omega, ?_, ?_⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · refine ⟨by simp, by simp, List.isChain_singleton _, ?_, ⟨x, rfl, hxA⟩, ⟨x, rfl, hxB⟩⟩
      intro v hv
      simp at hv
      exact hv ▸ hxS
    · exact (hL2 q hq).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
        (Finset.erase_subset _ _)
  · rw [List.pairwise_cons]
    refine ⟨fun q hq v hv hvq => ?_, hL3⟩
    simp at hv
    subst hv
    have := (hL2 q hq).2.2.2.1 v hvq
    exact (Finset.notMem_erase v S) this

/-- No common vertex and every minimum separator is `A` or `B`: delete an edge and induct. -/
theorem case_edge (G : SimpleGraph V) (S A B : Finset V) (k n : ℕ)
    (hμ : S.card + edgeCount G S ≤ n + 1) (hA : A ⊆ S) (hB : B ⊆ S)
    (hsep : ∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) (hk : k ≠ 0)
    (hX' : ∀ X, X ⊆ S → IsABSep G S A B X → X.card = k → X = A ∨ X = B)
    (hAB : ∀ x, x ∈ A → x ∈ B → False)
    (ih : ∀ (G : SimpleGraph V) (S A B : Finset V) (k : ℕ),
      S.card + edgeCount G S ≤ n → A ⊆ S → B ⊆ S →
      (∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) → HasLinkage G S A B k) :
    HasLinkage G S A B k := by
  classical
  have hex : ∃ p, IsABPath G S A B p := by
    by_contra hno
    push_neg at hno
    have hsp : IsABSep G S A B ∅ := fun p hp => absurd hp (hno p)
    have := hsep ∅ (Finset.empty_subset _) hsp
    simp at this
    exact hk this
  obtain ⟨p, hp⟩ := hex
  obtain ⟨p0, p1, rest, rfl⟩ : ∃ p0 p1 rest, p = p0 :: p1 :: rest := by
    rcases p with _ | ⟨p0, _ | ⟨p1, rest⟩⟩
    · exact absurd rfl hp.1
    · obtain ⟨a, ha, haA⟩ := hp.2.2.2.2.1
      obtain ⟨b, hb, hbB⟩ := hp.2.2.2.2.2
      simp at ha hb
      subst ha
      subst hb
      exact absurd haA (fun h => hAB _ h hbB)
    · exact ⟨p0, p1, rest, rfl⟩
  have hp0A : p0 ∈ A := by
    obtain ⟨a, ha, haA⟩ := hp.2.2.2.2.1
    simp at ha
    exact ha ▸ haA
  have hadj : G.Adj p0 p1 := (List.isChain_cons_cons.mp hp.2.2.1).1
  have hp0S : p0 ∈ S := hp.2.2.2.1 p0 (by simp)
  have hp1S : p1 ∈ S := hp.2.2.2.1 p1 (by simp)
  have hne01 : p0 ≠ p1 := hadj.ne
  have hμ' : S.card + edgeCount (G.deleteEdges {s(p0, p1)}) S ≤ n := by
    have := edgeCount_delete_lt hadj hp0S hp1S
    omega
  by_cases hG' : ∀ X, X ⊆ S → IsABSep (G.deleteEdges {s(p0, p1)}) S A B X → k ≤ X.card
  · obtain ⟨L, h1, h2, h3⟩ := ih (G.deleteEdges {s(p0, p1)}) S A B k hμ' hA hB hG'
    exact ⟨L, h1, fun q hq => (h2 q hq).mono_graph (SimpleGraph.deleteEdges_le _), h3⟩
  · push_neg at hG'
    obtain ⟨X', hX'S, hX'sep, hX'k⟩ := hG'
    have hins : ∀ y, (y = p0 ∨ y = p1) → IsABSep G S A B (insert y X') := by
      intro y hy q hq
      by_cases hboth : p0 ∈ q ∧ p1 ∈ q
      · refine ⟨y, Finset.mem_insert_self _ _, ?_⟩
        rcases hy with rfl | rfl
        · exact hboth.1
        · exact hboth.2
      · have hq' : IsABPath (G.deleteEdges {s(p0, p1)}) S A B q :=
          ⟨hq.1, hq.2.1, chain_delete q hq.2.2.1 hboth, hq.2.2.2.1, hq.2.2.2.2⟩
        obtain ⟨x, hx, hxq⟩ := hX'sep q hq'
        exact ⟨x, Finset.mem_insert_of_mem hx, hxq⟩
    have hsub : ∀ y, y ∈ S → insert y X' ⊆ S := fun y hy => Finset.insert_subset hy hX'S
    have hcard : ∀ y, (y = p0 ∨ y = p1) → y ∈ S → y ∉ X' ∧ (insert y X').card = k := by
      intro y hy hyS
      have h1 := hsep _ (hsub y hyS) (hins y hy)
      by_cases hyX : y ∈ X'
      · rw [Finset.insert_eq_of_mem hyX] at h1
        omega
      · refine ⟨hyX, ?_⟩
        rw [Finset.card_insert_of_notMem hyX] at h1 ⊢
        omega
    obtain ⟨hp0X, hc0⟩ := hcard p0 (Or.inl rfl) hp0S
    obtain ⟨hp1X, hc1⟩ := hcard p1 (Or.inr rfl) hp1S
    have h0 := hX' _ (hsub p0 hp0S) (hins p0 (Or.inl rfl)) hc0
    have h1 := hX' _ (hsub p1 hp1S) (hins p1 (Or.inr rfl)) hc1
    have hX1A : insert p0 X' = A := by
      rcases h0 with h | h
      · exact h
      · exact absurd (h ▸ Finset.mem_insert_self _ _) (fun hb => hAB p0 hp0A hb)
    have hX2B : insert p1 X' = B := by
      rcases h1 with h | h
      · exfalso
        have : p0 ∈ insert p1 X' := by rw [h, ← hX1A]; exact Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp this with h' | h'
        · exact hne01 h'
        · exact hp0X h'
      · exact h
    have hX'empty : X' = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      exact hAB x (hX1A ▸ Finset.mem_insert_of_mem hx) (hX2B ▸ Finset.mem_insert_of_mem hx)
    have hk1 : k = 1 := by
      rw [hX'empty] at hc0
      simpa using hc0.symm
    refine ⟨[[p0, p1]], by simp [hk1], ?_, by simp⟩
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    refine ⟨by simp, by simp [hne01], List.isChain_pair.mpr hadj, ?_, ⟨p0, rfl, hp0A⟩,
      ⟨p1, rfl, hX2B ▸ Finset.mem_insert_self _ _⟩⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl
    · exact hp0S
    · exact hp1S

theorem menger_aux : ∀ (n : ℕ) (G : SimpleGraph V) (S A B : Finset V) (k : ℕ),
    S.card + edgeCount G S ≤ n → A ⊆ S → B ⊆ S →
    (∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) → HasLinkage G S A B k := by
  intro n
  induction n with
  | zero =>
    intro G S A B k hμ hA hB hsep
    have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hS
    have hsp : IsABSep G ∅ A B ∅ := by
      intro p hp
      exfalso
      obtain ⟨hne, -, -, hS, -⟩ := hp
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil p hne
      simpa using hS v hv
    have := hsep ∅ (Finset.Subset.refl _) hsp
    have hk : k = 0 := by simpa using this
    subst hk
    exact ⟨[], rfl, by simp, List.Pairwise.nil⟩
  | succ n ih =>
    intro G S A B k hμ hA hB hsep
    by_cases hk : k = 0
    · subst hk; exact ⟨[], rfl, by simp, List.Pairwise.nil⟩
    by_cases hX : ∃ X, X ⊆ S ∧ IsABSep G S A B X ∧ X.card = k ∧ X ≠ A ∧ X ≠ B
    · obtain ⟨X, hXS, hXsep, hXk, hXA, hXB⟩ := hX
      exact case_split G S A B X k n hμ hA hB hsep hXS hXsep hXk hXA hXB ih
    · have hX' : ∀ X, X ⊆ S → IsABSep G S A B X → X.card = k → X = A ∨ X = B := by
        intro X hXS hXsep hXk
        by_contra hcon
        push_neg at hcon
        exact hX ⟨X, hXS, hXsep, hXk, hcon.1, hcon.2⟩
      by_cases hAB : ∃ x, x ∈ A ∧ x ∈ B
      · obtain ⟨x, hxA, hxB⟩ := hAB
        exact case_common G S A B k n hμ hA hB hsep x hxA hxB ih
      · exact case_edge G S A B k n hμ hA hB hsep hk hX'
          (fun x hxA hxB => hAB ⟨x, hxA, hxB⟩) ih

/-- Menger's theorem, set version (Diestel 3.3.1): if every `A`–`B` separator has at least `k`
vertices then there are `k` disjoint `A`–`B` paths. -/
theorem menger_set (G : SimpleGraph V) (S A B : Finset V) (hA : A ⊆ S) (hB : B ⊆ S) (k : ℕ)
    (hsep : ∀ X, X ⊆ S → IsABSep G S A B X → k ≤ X.card) : HasLinkage G S A B k :=
  menger_aux (S.card + edgeCount G S) G S A B k le_rfl hA hB hsep

end SPGTLib.Menger

namespace SPGTLib.ThreeTracks

open StrongPerfectGraph.LineGraph SPGTLib.Menger

variable {W : Type*}

/-- A duplicate-free list path avoiding a set, from connectivity of the induced graph on the
complement. -/
theorem path_avoiding [DecidableEq W] (J : SimpleGraph W) (Y : Set W)
    (hconn : (J.induce Yᶜ).Connected) {a c : W} (ha : a ∉ Y) (hc : c ∉ Y) :
    ∃ l : List W, l.head? = some a ∧ l.getLast? = some c ∧ l.Nodup ∧ List.IsChain J.Adj l ∧
      ∀ v ∈ l, v ∉ Y := by
  obtain ⟨w⟩ := hconn.preconnected ⟨a, ha⟩ ⟨c, hc⟩
  let P := w.toPath
  let L : List W := P.1.support.map Subtype.val
  refine ⟨L, ?_, ?_, P.2.support_nodup.map Subtype.val_injective,
    List.isChain_map_of_isChain Subtype.val (fun u v h => h) P.1.isChain_adj_support, ?_⟩
  · simp only [L, List.head?_map]
    rw [← SimpleGraph.Walk.cons_tail_support P.1]
    rfl
  · simp only [L, List.getLast?_map]
    rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil P.1),
      SimpleGraph.Walk.getLast_support]
    rfl
  · intro v hv
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hv
    exact s.2

/-- Any `{x, y}`–`N(c₂)` separator inside `V ∖ {c₁, c₂}` has at least two vertices. -/
theorem sep_two [Fintype W] [DecidableEq W] (J : SimpleGraph W) (hJ : IsThreeConnected J)
    (c₁ c₂ x y : W) (hx₂ : x ≠ c₂) (hy₂ : y ≠ c₂) (hxy : x ≠ y)
    (S A B : Finset W) (hS : ∀ v, v ∈ S ↔ v ≠ c₁ ∧ v ≠ c₂)
    (hA : A = {x, y}) (hB : ∀ v, v ∈ B ↔ J.Adj c₂ v ∧ v ≠ c₁)
    (hx₁ : x ≠ c₁) (hy₁ : y ≠ c₁) (hc : c₁ ≠ c₂)
    (X : Finset W) (hXS : X ⊆ S) (hXsep : IsABSep J S A B X) : 2 ≤ X.card := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, haA, haX⟩ : ∃ a, a ∈ A ∧ a ∉ X := by
    by_contra h
    push_neg at h
    have hxX := h x (by simp [hA])
    have hyX := h y (by simp [hA])
    have hsub : ({x, y} : Finset W) ⊆ X := by
      intro v hv
      simp at hv
      rcases hv with rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hxy] at this
    omega
  have haS : a ∈ S := by
    rw [hA] at haA
    simp at haA
    rcases haA with rfl | rfl
    · exact (hS _).mpr ⟨hx₁, hx₂⟩
    · exact (hS _).mpr ⟨hy₁, hy₂⟩
  have hac : a ≠ c₂ := ((hS a).mp haS).2
  set Y : Set W := ↑(insert c₁ X) with hY
  have hYcard : Y.ncard ≤ 2 := by
    rw [hY, Set.ncard_coe_finset]
    have := Finset.card_insert_le c₁ X
    omega
  have hconn := hJ.2 Y hYcard
  have haY : a ∉ Y := by
    simp only [hY, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or]
    exact ⟨((hS a).mp haS).1, haX⟩
  have hc2Y : c₂ ∉ Y := by
    simp only [hY, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or]
    exact ⟨hc.symm, fun h => ((hS c₂).mp (hXS h)).2 rfl⟩
  obtain ⟨l, hlh, hll, hlnd, hlch, hlY⟩ := path_avoiding J Y hconn haY hc2Y
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hll
  subst hys
  have hc2ys : c₂ ∉ ys := fun h => (List.nodup_append.mp hlnd).2.2 c₂ h c₂ (by simp) rfl
  have hysne : ys ≠ [] := by
    rintro rfl
    simp at hlh
    exact hac hlh.symm
  have hhead : ys.head? = some a := by
    rw [List.head?_append_of_ne_nil _ hysne] at hlh
    exact hlh
  have hpath : IsABPath J S A B ys := by
    refine ⟨hysne, (List.nodup_append.mp hlnd).1, (List.isChain_append.mp hlch).1, ?_,
      ⟨a, hhead, haA⟩, ?_⟩
    · intro v hv
      have hvY := hlY v (List.mem_append_left _ hv)
      simp only [hY, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or] at hvY
      exact (hS v).mpr ⟨hvY.1, fun h => hc2ys (h ▸ hv)⟩
    · obtain ⟨w, hw⟩ : ∃ w, ys.getLast? = some w :=
        ⟨_, List.getLast?_eq_some_getLast hysne⟩
      refine ⟨w, hw, ?_⟩
      have hadj := (List.isChain_append.mp hlch).2.2 w (by simpa using hw) c₂ (by simp)
      have hwv : w ∈ ys := List.mem_of_getLast? hw
      have hwY := hlY w (List.mem_append_left _ hwv)
      simp only [hY, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or] at hwY
      exact (hB w).mpr ⟨hadj.symm, hwY.1⟩
  obtain ⟨z, hzX, hzys⟩ := hXsep ys hpath
  have hzY := hlY z (List.mem_append_left _ hzys)
  exact hzY (by simp [hY, hzX])

end SPGTLib.ThreeTracks

namespace SPGTLib.ThreeTracks

open StrongPerfectGraph.LineGraph SPGTLib.Menger

variable {W : Type*}

/-- Closing an `A`–`B` path with `c₁` in front and `c₂` behind gives a track. -/
theorem track_of_path [DecidableEq W] (J : SimpleGraph W) (c₁ c₂ x : W) (hc : c₁ ≠ c₂)
    (S A B : Finset W) (hS : ∀ v, v ∈ S ↔ v ≠ c₁ ∧ v ≠ c₂)
    (hB : ∀ v, v ∈ B ↔ J.Adj c₂ v ∧ v ≠ c₁) (q : List W)
    (hP : IsABPath J S A B (x :: q)) (hx : J.Adj c₁ x) :
    IsTrack J (c₁ :: x :: q ++ [c₂]) := by
  obtain ⟨hne, hnd, hch, hSp, ⟨a, ha, haA⟩, ⟨b, hb, hbB⟩⟩ := hP
  have hc1 : c₁ ∉ x :: q := fun h => ((hS c₁).mp (hSp c₁ h)).1 rfl
  have hc2 : c₂ ∉ x :: q := fun h => ((hS c₂).mp (hSp c₂ h)).2 rfl
  refine ⟨by simp, ?_, ?_⟩
  · rw [List.cons_append, List.nodup_cons, List.nodup_append]
    refine ⟨fun h => ?_, hnd, List.nodup_singleton c₂, ?_⟩
    · rcases List.mem_append.mp h with h | h
      · exact hc1 h
      · simp at h; exact hc h
    · intro u hu v hv huv
      simp at hv
      subst hv
      exact hc2 (huv ▸ hu)
  · rw [List.cons_append]
    refine List.isChain_cons.mpr ⟨?_, ?_⟩
    · intro y hy
      rw [List.head?_append_of_ne_nil _ (List.cons_ne_nil x q)] at hy
      simp at hy
      subst hy
      exact hx
    · refine List.isChain_append.mpr ⟨hch, List.isChain_singleton _, ?_⟩
      intro u hu w hw
      simp at hw
      subst hw
      rw [hb] at hu
      have hub : u = b := (Option.some.inj hu).symm
      subst hub
      exact ((hB _).mp hbB).1.symm

/-- Two tracks through prescribed first vertices, from two disjoint `A`–`B` paths. -/
theorem tracks_of_two (J : SimpleGraph W) [DecidableEq W] (c₁ c₂ x y : W) (hc : c₁ ≠ c₂)
    (hx : J.Adj c₁ x) (hy : J.Adj c₁ y) (hxy : x ≠ y)
    (S A B : Finset W) (hS : ∀ v, v ∈ S ↔ v ≠ c₁ ∧ v ≠ c₂) (hA : A = {x, y})
    (hB : ∀ v, v ∈ B ↔ J.Adj c₂ v ∧ v ≠ c₁)
    (hL : HasLinkage J S A B 2) :
    ∃ q r : List W, IsTrack J (c₁ :: x :: q ++ [c₂]) ∧ IsTrack J (c₁ :: y :: r ++ [c₂]) ∧
      ∀ z ∈ x :: q, z ∉ y :: r := by
  obtain ⟨L, hlen, hLp, hpw⟩ := hL
  rcases L with _ | ⟨P, _ | ⟨Q, _ | ⟨R, rest⟩⟩⟩
  · simp at hlen
  · simp at hlen
  swap
  · simp at hlen
  have hP := hLp P (by simp)
  have hQ := hLp Q (by simp)
  have hdisj : ∀ v ∈ P, v ∉ Q := by
    rw [List.pairwise_cons] at hpw
    exact hpw.1 Q (by simp)
  have hP' := hP
  have hQ' := hQ
  obtain ⟨hPne, -, -, -, ⟨a1, ha1, ha1A⟩, -⟩ := hP
  obtain ⟨hQne, -, -, -, ⟨a2, ha2, ha2A⟩, -⟩ := hQ
  have key : ∀ (P Q : List W) (hP : IsABPath J S A B P) (hQ : IsABPath J S A B Q),
      P.head? = some x → Q.head? = some y → (∀ v ∈ P, v ∉ Q) →
      ∃ q r : List W, IsTrack J (c₁ :: x :: q ++ [c₂]) ∧ IsTrack J (c₁ :: y :: r ++ [c₂]) ∧
        ∀ z ∈ x :: q, z ∉ y :: r := by
    intro P Q hP hQ hPh hQh hd
    obtain ⟨q, rfl⟩ : ∃ q, P = x :: q := by
      rcases P with _ | ⟨a, q⟩
      · simp at hPh
      · simp at hPh; exact ⟨q, by rw [hPh]⟩
    obtain ⟨r, rfl⟩ : ∃ r, Q = y :: r := by
      rcases Q with _ | ⟨a, r⟩
      · simp at hQh
      · simp at hQh; exact ⟨r, by rw [hQh]⟩
    exact ⟨q, r, track_of_path J c₁ c₂ x hc S A B hS hB q hP hx,
      track_of_path J c₁ c₂ y hc S A B hS hB r hQ hy, hd⟩
  have hAxy : ∀ a, a ∈ A → a = x ∨ a = y := by
    intro a ha; rw [hA] at ha; simpa using ha
  rcases hAxy a1 ha1A with h1 | h1 <;> rcases hAxy a2 ha2A with h2 | h2
  · -- both heads equal x: contradiction with disjointness
    exfalso
    have hP1 : a1 ∈ P := List.mem_of_mem_head? ha1
    have hQ1 : a2 ∈ Q := List.mem_of_mem_head? ha2
    exact hdisj a1 hP1 (h1.trans h2.symm ▸ hQ1)
  · exact key P Q hP' hQ' (by rw [ha1, h1]) (by rw [ha2, h2]) hdisj
  · obtain ⟨q, r, h1', h2', h3⟩ := key Q P hQ' hP' (by rw [ha2, h2]) (by rw [ha1, h1])
      (fun v hv hvP => hdisj v hvP hv)
    exact ⟨q, r, h1', h2', h3⟩
  · exfalso
    have hP1 : a1 ∈ P := List.mem_of_mem_head? ha1
    have hQ1 : a2 ∈ Q := List.mem_of_mem_head? ha2
    exact hdisj a1 hP1 (h1.trans h2.symm ▸ hQ1)

end SPGTLib.ThreeTracks

open StrongPerfectGraph.LineGraph in
theorem solution {W : Type*} [Fintype W] (J : SimpleGraph W) (hJ : IsThreeConnected J)
    (c₁ c₂ x y : W) (h₁₂ : J.Adj c₁ c₂) (hx : J.Adj c₁ x) (hy : J.Adj c₁ y)
    (hx₂ : x ≠ c₂) (hy₂ : y ≠ c₂) (hxy : x ≠ y) :
    IsTrack J [c₁, c₂] ∧
      ∃ q r : List W, IsTrack J (c₁ :: x :: q ++ [c₂]) ∧ IsTrack J (c₁ :: y :: r ++ [c₂]) ∧
        ∀ z ∈ x :: q, z ∉ y :: r := by
  classical
  have hc : c₁ ≠ c₂ := h₁₂.ne
  refine ⟨⟨by simp, by simp [hc], by simpa using h₁₂⟩, ?_⟩
  let S : Finset W := Finset.univ.filter (fun v => v ≠ c₁ ∧ v ≠ c₂)
  let A : Finset W := {x, y}
  let B : Finset W := Finset.univ.filter (fun v => J.Adj c₂ v ∧ v ≠ c₁)
  have hS : ∀ v, v ∈ S ↔ v ≠ c₁ ∧ v ≠ c₂ := by intro v; simp [S]
  have hB : ∀ v, v ∈ B ↔ J.Adj c₂ v ∧ v ≠ c₁ := by intro v; simp [B]
  have hx₁ : x ≠ c₁ := hx.ne.symm
  have hy₁ : y ≠ c₁ := hy.ne.symm
  have hAS : A ⊆ S := by
    intro v hv
    simp [A] at hv
    rcases hv with rfl | rfl
    · exact (hS _).mpr ⟨hx₁, hx₂⟩
    · exact (hS _).mpr ⟨hy₁, hy₂⟩
  have hBS : B ⊆ S := by
    intro v hv
    obtain ⟨hadj, hv1⟩ := (hB v).mp hv
    exact (hS v).mpr ⟨hv1, hadj.ne.symm⟩
  have hsep := fun X (hXS : X ⊆ S) (hXsep : SPGTLib.Menger.IsABSep J S A B X) =>
    SPGTLib.ThreeTracks.sep_two J hJ c₁ c₂ x y hx₂ hy₂ hxy S A B hS rfl hB hx₁ hy₁ hc X hXS hXsep
  have hL := SPGTLib.Menger.menger_set J S A B hAS hBS 2 hsep
  exact SPGTLib.ThreeTracks.tracks_of_two J c₁ c₂ x y hc hx hy hxy S A B hS rfl hB hL
