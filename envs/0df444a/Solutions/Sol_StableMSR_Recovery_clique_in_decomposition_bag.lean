-- Prove2me | solution 1 for StableMSR.Recovery.clique_in_decomposition_bag
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T16:10:14.957358+00:00
-- url     : https://prove2.me/submissions/755f7b36-8e38-4763-9c1f-8f86cff9a123

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.TreeHelly

/- A set contains the unique tree path between any two of its vertices. -/
def PathConvex {T : Type} (tree : SimpleGraph T) (C : Finset T) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ p : tree.Walk x y, p.IsPath → ∀ z ∈ p.support, z ∈ C

lemma leaf_neighbor_mem {T : Type} [Fintype T] [DecidableEq T]
    (tree : SimpleGraph T) (htree : tree.IsTree) {v w : T}
    (hadj : tree.Adj v w) (huniq : ∀ u, tree.Adj v u → u = w)
    (C : Finset T) (hc : PathConvex tree C) (hv : v ∈ C) (hC : C ≠ {v}) :
    w ∈ C := by
  classical
  obtain ⟨x, hx, hxv⟩ : ∃ x ∈ C, x ≠ v := by
    by_contra hn
    apply hC
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro hx
      by_contra hne
      exact hn ⟨x, hx, hne⟩
    · rintro rfl
      exact hv
  obtain ⟨p, hp⟩ := htree.connected.exists_isPath v x
  have hnil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hxv.symm
  have hw : p.snd = w := huniq _ (p.adj_snd hnil)
  exact hw ▸ hc v hv x hx p hp p.snd (List.mem_of_mem_tail (p.snd_mem_tail_support hnil))

/- The Helly property for arbitrary families of nonempty path-convex subsets
of a finite tree. The index type need not be finite. -/
theorem finite_tree_helly {T : Type} [Fintype T] [DecidableEq T]
    (tree : SimpleGraph T) (htree : tree.IsTree) {I : Type*}
    (C : I → Finset T) (hne : ∀ i, (C i).Nonempty)
    (hconv : ∀ i, PathConvex tree (C i))
    (hpair : ∀ i j, ((C i) ∩ (C j)).Nonempty) :
    ∃ t : T, ∀ i, t ∈ C i := by
  classical
  have aux : ∀ n : ℕ, ∀ (T : Type) [Fintype T] [DecidableEq T],
      Fintype.card T = n → ∀ (tree : SimpleGraph T), tree.IsTree →
      ∀ (C : I → Finset T), (∀ i, (C i).Nonempty) →
      (∀ i, PathConvex tree (C i)) →
      (∀ i j, ((C i) ∩ (C j)).Nonempty) → ∃ t : T, ∀ i, t ∈ C i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T _ _ hcard tree ht C hne hc hp
      by_cases hsub : Subsingleton T
      · obtain ⟨t⟩ := ht.connected.nonempty
        refine ⟨t, ?_⟩
        intro i
        obtain ⟨x, hx⟩ := hne i
        exact (hsub.elim x t) ▸ hx
      · letI : Nontrivial T := not_subsingleton_iff_nontrivial.mp hsub
        obtain ⟨v, hvdeg⟩ := ht.exists_vert_degree_one_of_nontrivial
        obtain ⟨w, hvw, hw⟩ := tree.degree_eq_one_iff_existsUnique_adj.mp hvdeg
        by_cases hsing : ∃ i, C i = {v}
        · obtain ⟨i, hi⟩ := hsing
          refine ⟨v, ?_⟩
          intro j
          obtain ⟨x, hx⟩ := hp i j
          obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
          rw [hi, Finset.mem_singleton] at hxi
          exact hxi ▸ hxj
        · have hnot : ∀ i, C i ≠ {v} := by simpa only [not_exists] using hsing
          let U : Set T := {v}ᶜ
          let tree' := tree.induce U
          have ht' : tree'.IsTree :=
            ⟨ht.connected.induce_compl_singleton_of_degree_eq_one hvdeg, ht.isAcyclic.induce U⟩
          let C' : I → Finset U := fun i => Finset.univ.filter (fun x => x.val ∈ C i)
          have hne' : ∀ i, (C' i).Nonempty := by
            intro i
            obtain ⟨x, hx⟩ := hne i
            by_cases hxv : x = v
            · have hvC : v ∈ C i := hxv ▸ hx
              have hwC := leaf_neighbor_mem tree ht hvw hw (C i) (hc i) hvC (hnot i)
              refine ⟨⟨w, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwC⟩⟩
              exact fun heq => tree.ne_of_adj hvw heq.symm
            · exact ⟨⟨x, hxv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
          have hc' : ∀ i, PathConvex tree' (C' i) := by
            intro i x hx y hy p hpath z hz
            have hxC := (Finset.mem_filter.mp hx).2
            have hyC := (Finset.mem_filter.mp hy).2
            let f : tree' →g tree := {toFun := Subtype.val, map_rel' := by intro x y h; exact h}
            have hpath' : (p.map f).IsPath := hpath.map Subtype.val_injective
            have hz' : z.val ∈ (p.map f).support := by
              rw [SimpleGraph.Walk.support_map]
              exact List.mem_map.mpr ⟨z, hz, rfl⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc i x.val hxC y.val hyC
              (p.map f) hpath' z.val hz'⟩
          have hp' : ∀ i j, (C' i ∩ C' j).Nonempty := by
            intro i j
            obtain ⟨x, hx⟩ := hp i j
            obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
            by_cases hxv : x = v
            · have hi := leaf_neighbor_mem tree ht hvw hw (C i) (hc i) (hxv ▸ hxi) (hnot i)
              have hj := leaf_neighbor_mem tree ht hvw hw (C j) (hc j) (hxv ▸ hxj) (hnot j)
              exact ⟨⟨w, fun heq => tree.ne_of_adj hvw heq.symm⟩,
                Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩⟩
            · exact ⟨⟨x, hxv⟩, Finset.mem_inter.mpr
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxj⟩⟩⟩
          have hlt : Fintype.card U < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (x := v) (by simp [U])
          obtain ⟨t, htC⟩ := ih (Fintype.card U) hlt U rfl tree' ht' C' hne' hc' hp'
          exact ⟨t.val, fun i => (Finset.mem_filter.mp (htC i)).2⟩
  exact aux (Fintype.card T) T rfl tree htree C hne hconv hpair

/- Every clique of graph vertices is covered by one bag of the canonical
tree decomposition, including the empty clique. -/
theorem clique_subset_bag {V T : Type} [DecidableEq V] [Fintype T] [DecidableEq T]
    (G : SimpleGraph V) (tree : SimpleGraph T) (bags : T → Finset V)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    (K : Finset V) (hK : (K : Set V).Pairwise G.Adj) :
    ∃ t : T, K ⊆ bags t := by
  classical
  let C : K → Finset T := fun v => Finset.univ.filter (fun t => v.val ∈ bags t)
  have hne : ∀ v, (C v).Nonempty := by
    intro v
    obtain ⟨t, ht⟩ := htd.2.1 v.val
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
  have hconv : ∀ v, PathConvex tree (C v) := by
    intro v x hx y hy p hp z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      htd.2.2.2 x z y p hp hz (Finset.mem_inter.mpr
        ⟨(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2⟩)⟩
  have hpair : ∀ v w, (C v ∩ C w).Nonempty := by
    intro v w
    by_cases heq : v = w
    · subst w
      simpa only [Finset.inter_self] using hne v
    · have hadj := hK v.property w.property (fun h => heq (Subtype.ext h))
      obtain ⟨t, htv, htw⟩ := htd.2.2.1 v.val w.val hadj
      exact ⟨t, Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, htv⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, htw⟩⟩⟩
  obtain ⟨t, ht⟩ := finite_tree_helly tree htd.1 C hne hconv hpair
  exact ⟨t, fun v hv => (Finset.mem_filter.mp (ht ⟨v, hv⟩)).2⟩

end StableMSR.Recovery.TreeHelly


open StableMSR.Recovery

theorem solution {V T : Type} [DecidableEq V] [Fintype T] [DecidableEq T]
    (G : SimpleGraph V) (tree : SimpleGraph T) (bags : T → Finset V)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    (K : Finset V) (hK : (K : Set V).Pairwise G.Adj) :
    ∃ t : T, K ⊆ bags t := by
  exact TreeHelly.clique_subset_bag G tree bags htd K hK
