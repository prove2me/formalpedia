-- Prove2me | solution 1 for PadbergRao.OddCut.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:10:04.240169+00:00
-- url     : https://prove2.me/submissions/8b885892-ec79-406f-8aa3-9711ecb71ff2

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Ring.Nat
import Definitions.Def_PadbergRao_OddCut_IsOddMinCut
import Definitions.Def_PadbergRao_OddCut_IsOddCutTree

open Finset SimpleGraph

set_option autoImplicit false

namespace OddCutProof

noncomputable def side {V : Type*} [Fintype V] (G : SimpleGraph V) (a b : V) : Finset V := by
  classical
  exact univ.filter fun x => (G.deleteEdges {s(a, b)}).Reachable a x

@[simp] lemma mem_side {V : Type*} [Fintype V] (G : SimpleGraph V) (a b x : V) :
    x ∈ side G a b ↔ (G.deleteEdges {s(a, b)}).Reachable a x := by
  classical
  simp [side]

lemma end_not_side {V : Type*} [Fintype V] (G : SimpleGraph V) (ht : G.IsTree)
    {a b : V} (hab : G.Adj a b) : b ∉ side G a b := by
  rw [mem_side]
  exact isAcyclic_iff_forall_adj_isBridge.mp ht.isAcyclic hab

lemma sides_cover {V : Type*} [Fintype V] (G : SimpleGraph V) (ht : G.IsTree)
    (a b x : V) : x ∈ side G a b ∨ x ∈ side G b a := by
  classical
  simp only [mem_side]
  have hswap : G.deleteEdges {s(b, a)} = G.deleteEdges {s(a, b)} := by
    rw [Sym2.eq_swap]
  rw [hswap]
  have hp := (reachable_iff_reflTransGen a x).mp (ht.connected a x)
  induction hp with
  | refl => exact Or.inl .rfl
  | @tail y z _ hyz ih =>
    by_cases he : s(y, z) = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr .rfl
      · exact Or.inl .rfl
    · have hd : (G.deleteEdges {s(a, b)}).Adj y z :=
        deleteEdges_adj.mpr ⟨hyz, by simpa using he⟩
      exact ih.elim (fun h => Or.inl (h.trans hd.reachable))
        (fun h => Or.inr (h.trans hd.reachable))

lemma side_compl {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ht : G.IsTree)
    {a b : V} (hab : G.Adj a b) : (side G a b)ᶜ = side G b a := by
  classical
  ext x
  constructor
  · intro hx
    exact (sides_cover G ht a b x).resolve_left (mem_compl.mp hx)
  · intro hx
    apply mem_compl.mpr
    intro hx'
    have h₁ := (mem_side G a b x).mp hx'
    have h₂ := (mem_side G b a x).mp hx
    have hswap : G.deleteEdges {s(b, a)} = G.deleteEdges {s(a, b)} := by
      rw [Sym2.eq_swap]
    rw [hswap] at h₂
    exact end_not_side G ht hab ((mem_side G a b b).mpr (h₁.trans h₂.symm))

lemma reach_avoid_incident {V : Type*} (G : SimpleGraph V) {a b r s : V}
    (hab : G.Reachable a b) (hn : ¬ G.Reachable a r) :
    (G.deleteEdges {s(r, s)}).Reachable a b := by
  classical
  obtain ⟨p⟩ := hab
  apply reachable_deleteEdges_iff_exists_walk.mpr
  refine ⟨p, ?_⟩
  intro he
  exact hn (p.takeUntil r (p.fst_mem_support_of_mem_edges he)).reachable

lemma branch_cover {V : Type*} [Fintype V] (G : SimpleGraph V) (ht : G.IsTree)
    (r x : V) (hx : x ≠ r) : ∃ s, G.Adj r s ∧ x ∈ side G s r := by
  classical
  obtain ⟨p, hp⟩ := (ht.connected r x).exists_isPath
  cases p with
  | nil => exact (hx rfl).elim
  | @cons r s x hrs p =>
    refine ⟨s, hrs, (mem_side G s r x).mpr ?_⟩
    apply reachable_deleteEdges_iff_exists_walk.mpr
    refine ⟨p, ?_⟩
    intro he
    exact (Walk.cons_isPath_iff hrs p).mp hp |>.2 (p.snd_mem_support_of_mem_edges he)

lemma branch_disjoint {V : Type*} [Fintype V] (G : SimpleGraph V) (ht : G.IsTree)
    {r a b : V} (hra : G.Adj r a) (hrb : G.Adj r b) (hab : a ≠ b) :
    Disjoint (side G a r) (side G b r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hax hbx
  have har : ¬ (G.deleteEdges {s(a, r)}).Reachable a r :=
    isAcyclic_iff_forall_adj_isBridge.mp ht.isAcyclic hra.symm
  have hax' := reach_avoid_incident (G.deleteEdges {s(a, r)})
    ((mem_side G a r x).mp hax) (s := b) har
  have hax'' : (G.deleteEdges {s(r, b)}).Reachable a x :=
    hax'.mono (deleteEdges_mono (G.deleteEdges_le _))
  have hra' : (G.deleteEdges {s(r, b)}).Adj r a := by
    apply deleteEdges_adj.mpr
    refine ⟨hra, ?_⟩
    simp [hra.ne.symm, hab]
  have hbx' := (mem_side G b r x).mp hbx
  have hswap : G.deleteEdges {s(b, r)} = G.deleteEdges {s(r, b)} := by
    rw [Sym2.eq_swap]
  rw [hswap] at hbx'
  exact end_not_side G ht hrb ((mem_side G r b b).mpr
    (hra'.reachable.trans (hax''.trans hbx'.symm)))

lemma branch_card_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ht : G.IsTree)
    (r : V) : (∑ s ∈ univ.filter (G.Adj r), (side G s r).card) + 1 =
      Fintype.card V := by
  classical
  let N := univ.filter (G.Adj r)
  have hd : (N : Set V).PairwiseDisjoint (fun s => side G s r) := by
    intro a ha b hb hab
    exact branch_disjoint G ht (mem_filter.mp ha).2 (mem_filter.mp hb).2 hab
  have hu : N.biUnion (fun s => side G s r) = ({r} : Finset V)ᶜ := by
    ext x
    simp only [mem_biUnion, mem_compl, mem_singleton]
    constructor
    · rintro ⟨s, hs, hx⟩ rfl
      exact end_not_side G ht (mem_filter.mp hs).2.symm hx
    · intro hx
      obtain ⟨s, hs, hx⟩ := branch_cover G ht r x hx
      exact ⟨s, by simp [N, hs], hx⟩
  have hcard := card_biUnion hd
  rw [hu] at hcard
  change (∑ s ∈ N, (side G s r).card) + 1 = _
  rw [← hcard]
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
  simp only [card_compl, card_singleton]
  omega

lemma side_odd_swap {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ht : G.IsTree) (he : Even (Fintype.card V))
    {a b : V} (hab : G.Adj a b) :
    Odd (side G a b).card ↔ Odd (side G b a).card := by
  have hc := card_compl (side G a b)
  rw [side_compl G ht hab] at hc
  have hb := card_le_univ (side G a b)
  rw [Nat.even_iff] at he
  simp only [Nat.odd_iff]
  omega

noncomputable def oddGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ht : G.IsTree) (he : Even (Fintype.card V)) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ Odd (side G a b).card
  symm := ⟨fun _ _ h => ⟨h.1.symm, (side_odd_swap G ht he h.1).mp h.2⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

set_option maxHeartbeats 1000000 in
/-- Every odd set in an even-order tree crosses an edge whose two shores are odd. -/
lemma odd_set_crosses_odd_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ht : G.IsTree) (he : Even (Fintype.card V))
    (U : Finset V) (hU : Odd U.card) :
    ∃ a b : V, G.Adj a b ∧ Odd (side G a b).card ∧ a ∈ U ∧ b ∉ U := by
  classical
  let F := oddGraph G ht he
  have hdeg : ∀ r : V, Odd (F.degree r) := by
    intro r
    have hsum := branch_card_sum G ht r
    have hodd : Odd (∑ s ∈ univ.filter (G.Adj r), (side G s r).card) := by
      rw [Nat.odd_iff]
      have he' := Nat.even_iff.mp he
      omega
    have hcount := (odd_sum_iff_odd_card_odd (fun s => (side G s r).card)).mp hodd
    have hneigh : F.neighborFinset r =
        (univ.filter (G.Adj r)).filter (fun s => Odd (side G s r).card) := by
      ext s
      simp only [mem_neighborFinset, mem_filter, mem_univ, true_and]
      change (G.Adj r s ∧ Odd (side G r s).card) ↔
        G.Adj r s ∧ Odd (side G s r).card
      exact and_congr_right fun hrs => side_odd_swap G ht he hrs
    rw [← card_neighborFinset_eq_degree, hneigh]
    exact hcount
  by_contra h
  have hclosed : ∀ a ∈ U, ∀ b, F.Adj a b → b ∈ U := by
    intro a ha b hab
    by_contra hb
    exact h ⟨a, b, hab.1, hab.2, ha, hb⟩
  let K := F.induce (U : Set V)
  have hkdeg : ∀ a : (U : Set V), Odd (K.degree a) := by
    intro a
    have hn : F.neighborSet a ⊆ (U : Set V) := by
      intro b hb
      exact hclosed a a.property b hb
    have hd : K.degree a = F.degree a := by
      convert! degree_induce_of_neighborSet_subset (G := F) (s := (U : Set V)) (v := a) hn
    rw [hd]
    exact hdeg a
  have hk := K.even_card_odd_degree_vertices
  have hfilter : univ.filter (fun a : (U : Set V) => Odd (K.degree a)) = univ := by
    ext a
    simp [hkdeg a]
  rw [hfilter, card_univ] at hk
  have hcard : Fintype.card (U : Set V) = U.card := Fintype.card_coe U
  rw [hcard] at hk
  exact (Nat.not_even_iff_odd.mpr hU) hk

end OddCutProof

open Finset PadbergRao.OddCut

set_option autoImplicit false

private noncomputable def terminalSet {V : Type*} [DecidableEq V]
    (odd U : Finset V) : Finset {v // v ∈ odd} := by
  classical
  exact odd.attach.filter fun v => (v : V) ∈ U

private lemma terminal_card {V : Type*} [Fintype V] [DecidableEq V]
    (odd U : Finset V) : (terminalSet odd U).card = (U ∩ odd).card := by
  classical
  unfold terminalSet
  apply card_bij (fun (v : {v // v ∈ odd}) _ => (v : V))
  · intro v hv
    exact mem_inter.mpr ⟨(mem_filter.mp hv).2, v.property⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro v hv
    exact ⟨⟨v, (mem_inter.mp hv).2⟩, by simp [(mem_inter.mp hv).1], rfl⟩

private lemma odd_shore {V : Type*} [Fintype V] [DecidableEq V]
    (odd : Finset V) (H : SimpleGraph {v // v ∈ odd}) (π : V → {v // v ∈ odd})
    (hfix : ∀ r : {v // v ∈ odd}, π r = r) (r s : {v // v ∈ odd})
    (ho : Odd (subtree H r s).card) : IsOddSet odd (shore H π r s) := by
  classical
  unfold IsOddSet
  rw [← terminal_card odd (shore H π r s)]
  have hf : terminalSet odd (shore H π r s) =
      subtree H r s := by
    ext v
    simp [terminalSet, shore, hfix v]
  rw [hf]
  exact ho

private lemma side_eq_subtree {V : Type*} [Fintype V] [DecidableEq V]
    (odd : Finset V) (H : SimpleGraph {v // v ∈ odd}) (r s : {v // v ∈ odd}) :
    OddCutProof.side H r s = subtree H r s := by
  classical
  ext v
  simp [OddCutProof.side, subtree]

/-- Padberg–Rao Theorem 1.1: a lightest odd-splitting cut-tree edge is a minimum odd cut. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (_hc_symm : ∀ i j, c i j = c j i) (_hc_nonneg : ∀ i j, 0 ≤ c i j)
    (odd : Finset V) (hodd_ne : odd.Nonempty) (hodd_even : Even odd.card)
    (H : SimpleGraph {v // v ∈ odd}) (π : V → {v // v ∈ odd})
    (hT : IsOddCutTree c odd H π) :
    (∃ r s : {v // v ∈ odd}, H.Adj r s ∧ Odd (subtree H r s).card) ∧
    ∀ r s : {v // v ∈ odd}, H.Adj r s → Odd (subtree H r s).card →
      (∀ r' s' : {v // v ∈ odd}, H.Adj r' s' → Odd (subtree H r' s').card →
        treeEdgeWeight c H π r s ≤ treeEdgeWeight c H π r' s') →
      IsOddMinCut c odd (shore H π r s) := by
  classical
  have he : Even (Fintype.card {v // v ∈ odd}) := by simpa using hodd_even
  constructor
  · obtain ⟨v, hv⟩ := hodd_ne
    obtain ⟨r, s, hrs, ho, _, _⟩ := OddCutProof.odd_set_crosses_odd_edge H hT.1 he
      {⟨v, hv⟩} (by simp)
    exact ⟨r, s, hrs, by rwa [side_eq_subtree odd H r s] at ho⟩
  · intro r s _hrs ho hmin
    refine ⟨odd_shore odd H π hT.2.1 r s ho, ?_⟩
    intro U hU
    let UT : Finset {v // v ∈ odd} := terminalSet odd U
    have hUT : Odd UT.card := by
      change Odd (terminalSet odd U).card
      rw [terminal_card odd U]
      exact hU
    obtain ⟨a, b, hab, habodd, ha, hb⟩ :=
      OddCutProof.odd_set_crosses_odd_edge H hT.1 he UT hUT
    have hodd : Odd (subtree H a b).card := by
      rwa [side_eq_subtree odd H a b] at habodd
    have haU : (a : V) ∈ U := by simpa [UT, terminalSet] using ha
    have hbU : (b : V) ∉ U := by simpa [UT, terminalSet] using hb
    exact (hmin a b hab hodd).trans (hT.2.2 a b hab U haU hbU)
