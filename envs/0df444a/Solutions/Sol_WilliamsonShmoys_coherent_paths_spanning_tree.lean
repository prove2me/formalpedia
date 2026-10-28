-- Prove2me | solution 1 for WilliamsonShmoys.coherent_paths_spanning_tree
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:24:17.579861+00:00
-- url     : https://prove2.me/submissions/73c7ae5c-afba-4fb1-94c7-a9debd81b208

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

namespace A3S56ST
open SimpleGraph

lemma isPath_iff_eq_nil' {V : Type} {G : SimpleGraph V} {u : V} {p : G.Walk u u} :
    p.IsPath ↔ p = SimpleGraph.Walk.nil := by
  rw [Walk.isPath_iff_nil, Walk.eq_nil_iff_nil]

lemma takeUntil_end_of_isPath {V : Type} [DecidableEq V] {G : SimpleGraph V} {u x : V} (a : G.Walk u x)
    (ha : a.IsPath) (h : x ∈ a.support) : a.takeUntil x h = a := by
  induction a with
  | nil => simp
  | @cons u' w x' hadj a' ih =>
    rw [Walk.cons_isPath_iff] at ha
    have hne : u' ≠ x' := fun he => ha.2 (he ▸ a'.end_mem_support)
    rw [Walk.takeUntil_cons a'.end_mem_support hne, ih ha.1]

lemma eq_takeUntil {V : Type} [DecidableEq V] {G : SimpleGraph V} {u x v : V} (p : G.Walk u v)
    (hp : p.IsPath) (a : G.Walk u x) (r : G.Walk x v) (heq : p = a.append r)
    (h : x ∈ p.support) : a = p.takeUntil x h := by
  subst heq
  rw [Walk.takeUntil_append_of_mem_left a r a.end_mem_support,
    takeUntil_end_of_isPath a (hp.of_append_left) _]

end A3S56ST

open A3S56ST in
theorem solution
    {V : Type} [Fintype V] (G : SimpleGraph V) (root : V)
    (P : (v : {x : V // G.Reachable root x}) → G.Walk root v.val)
    (hpath : ∀ v, (P v).IsPath)
    (hprefix : ∀ u v : {x : V // G.Reachable root x},
      u.val ∈ (P v).support → (P u).IsSubwalk (P v)) :
    ∃ (R : SimpleGraph {x : V // G.Reachable root x}),
      R ≤ G.induce {x : V | G.Reachable root x} ∧ R.IsTree ∧
      ∃ (Q : (v : {x : V // G.Reachable root x}) →
          R.Walk ⟨root, SimpleGraph.Reachable.refl root⟩ v),
        (∀ v, (Q v).IsPath) ∧
        (∀ u v : {x : V // G.Reachable root x},
          u ∈ (Q v).support ↔ u.val ∈ (P v).support) := by
  classical
  set V' := {x : V // G.Reachable root x}
  set r' : V' := ⟨root, SimpleGraph.Reachable.refl root⟩
  -- key prefix fact
  have hpre : ∀ u v : V', ∀ h : u.val ∈ (P v).support, P u = (P v).takeUntil u.val h := by
    intro u v h
    obtain ⟨ru, rv, he⟩ := hprefix u v h
    have hru : ru.IsPath := by
      have := hpath v; rw [he] at this; exact this.of_append_left.of_append_left
    rw [isPath_iff_eq_nil'] at hru
    subst hru
    exact eq_takeUntil _ (hpath v) (P u) rv (by simpa using he) h
  let par : V' → V' := fun y => ⟨(P y).penultimate, ⟨(P y).dropLast⟩⟩
  have hnil : ∀ y : V', y ≠ r' → ¬ (P y).Nil := by
    intro y hy hn
    apply hy
    exact Subtype.ext hn.eq.symm
  have hA : ∀ y : V', y ≠ r' → G.Adj (par y).val y.val := fun y hy =>
    SimpleGraph.Walk.adj_penultimate (hnil y hy)
  have hB : ∀ y : V', y ≠ r' → P (par y) = (P y).dropLast := by
    intro y hy
    have hmem : (par y).val ∈ (P y).support := by
      have := congrArg SimpleGraph.Walk.support (SimpleGraph.Walk.concat_dropLast (hA y hy))
      rw [← this, SimpleGraph.Walk.support_concat]
      simp only [List.mem_append, List.mem_singleton]
      exact Or.inl (SimpleGraph.Walk.end_mem_support _)
    rw [hpre (par y) y hmem]
    symm
    apply eq_takeUntil _ (hpath y) _ (SimpleGraph.Walk.cons (hA y hy) SimpleGraph.Walk.nil)
    rw [← SimpleGraph.Walk.concat_eq_append, SimpleGraph.Walk.concat_dropLast]
  have hC : ∀ y : V', y ≠ r' → (P y).support = (P (par y)).support ++ [y.val] := by
    intro y hy
    rw [hB y hy]
    have := congrArg SimpleGraph.Walk.support (SimpleGraph.Walk.concat_dropLast (hA y hy))
    rw [SimpleGraph.Walk.support_concat] at this
    simpa using this.symm
  have hD : ∀ y : V', y ≠ r' → (P (par y)).length + 1 = (P y).length := by
    intro y hy
    rw [hB y hy]
    exact SimpleGraph.Walk.length_dropLast_add_one (hnil y hy)
  let R : SimpleGraph V' := SimpleGraph.fromRel (fun a b => b ≠ r' ∧ a = par b)
  have hRadj : ∀ y : V', y ≠ r' → R.Adj (par y) y := by
    intro y hy
    refine ⟨?_, Or.inl ⟨hy, rfl⟩⟩
    intro h
    exact (hA y hy).ne (congrArg Subtype.val h)
  have hQ : ∀ n, ∀ v : V', (P v).length = n →
      ∃ q : R.Walk r' v, q.support.map Subtype.val = (P v).support := by
    intro n
    induction n with
    | zero =>
      intro v hv
      have hvr : v = r' := by
        apply Subtype.ext
        exact (SimpleGraph.Walk.eq_of_length_eq_zero hv).symm
      subst hvr
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      have h0 := isPath_iff_eq_nil'.mp (hpath r')
      rw [h0]
      rfl
    | succ n ih =>
      intro v hv
      have hvr : v ≠ r' := by
        rintro rfl
        have h0 := isPath_iff_eq_nil'.mp (hpath r')
        rw [h0] at hv
        simp at hv
      obtain ⟨q, hq⟩ := ih (par v) (by have := hD v hvr; omega)
      refine ⟨q.concat (hRadj v hvr), ?_⟩
      rw [SimpleGraph.Walk.support_concat, hC v hvr, ← hq]
      simp
  choose Q hQ' using fun v => hQ _ v rfl
  have hQpath : ∀ v, (Q v).IsPath := by
    intro v
    rw [SimpleGraph.Walk.isPath_def]
    have := (hpath v).support_nodup
    rw [← hQ' v] at this
    exact this.of_map _
  have hconn : R.Connected := by
    have : Nonempty V' := ⟨r'⟩
    exact ⟨fun a b => ⟨(Q a).reverse.append (Q b)⟩⟩
  refine ⟨R, ?_, ?_, Q, hQpath, ?_⟩
  · intro a b h
    show G.Adj a.val b.val
    rcases h with ⟨_, ⟨hb, rfl⟩ | ⟨ha, rfl⟩⟩
    · exact hA b hb
    · exact (hA a ha).symm
  · rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨hconn, le_antisymm ?_ hconn.card_vert_le_card_edgeSet_add_one⟩
    let f : {a : V' // a ≠ r'} → R.edgeSet := fun a => ⟨s(par a.1, a.1), hRadj a.1 a.2⟩
    have hf : Function.Surjective f := by
      rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ a b =>
        simp only [SimpleGraph.mem_edgeSet, R, SimpleGraph.fromRel_adj] at he
        rcases he with ⟨_, ⟨hb, h⟩ | ⟨ha, h⟩⟩
        · subst h; exact ⟨⟨b, hb⟩, rfl⟩
        · subst h; exact ⟨⟨a, ha⟩, Subtype.ext Sym2.eq_swap⟩
    have h1 := Nat.card_le_card_of_surjective f hf
    have h2 : Nat.card {a : V' // a ≠ r'} + 1 = Nat.card V' := by
      simp only [Nat.card_eq_fintype_card]
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      have : 0 < Fintype.card V' := Fintype.card_pos_iff.mpr ⟨r'⟩
      omega
    have h3 : Nat.card R.edgeSet + 1 ≤ Nat.card V' := by omega
    exact h3
  · intro u v
    rw [← hQ' v, List.mem_map]
    constructor
    · intro h; exact ⟨u, h, rfl⟩
    · rintro ⟨w, hw, he⟩
      rwa [← Subtype.ext he]
