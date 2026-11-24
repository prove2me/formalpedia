-- Prove2me | solution 1 for SimpleGraph.IsTree.girth_add_one_le_card_of_two_leaves_of_two_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:31:59.800736+00:00
-- url     : https://prove2.me/submissions/da5f5d5e-986a-4b3d-9e76-f5fdeb4e2db2

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Set.Finite.Lemmas
public import Definitions.Def_Wowii84_LargestInducedTree

set_option autoImplicit false
@[expose] public section
public section
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace SimpleGraph
namespace IsTree
theorem _root_.solution
    {G : SimpleGraph α} [DecidableRel G.Adj] {s : Finset α}
    (hT : (G.induce (s : Set α)).IsTree)
    {x y z a b : α}
    (hxs : x ∈ s) (hys : y ∈ s) (hxy : x ≠ y)
    (hx : G.degree x = 1) (hy : G.degree y = 1)
    (hz : z ∉ s) (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hza : G.Adj z a) (hzb : G.Adj z b) :
    G.girth + 1 ≤ s.card := by
  let e : G.induce (s : Set α) ↪g G := SimpleGraph.Embedding.induce _
  obtain ⟨p, hp, _⟩ := hT.existsUnique_path ⟨a, by simpa⟩ ⟨b, by simpa⟩
  let q : G.Walk a b := p.map e.toHom
  have hq : q.IsPath := by
    dsimp [q]
    exact (Walk.isPath_map_iff_of_injective e.injective).2 hp
  have hq_s : ∀ w ∈ q.support, w ∈ s := by
    intro w hw
    change w ∈ (p.map e.toHom).support at hw
    rw [Walk.support_map] at hw
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
    exact w'.property
  have hzq : z ∉ q.support := fun hzmem => hz (hq_s z hzmem)
  let r : G.Walk a z := q.concat hzb.symm
  have hr : r.IsPath := hq.concat hzq hzb.symm
  have hclose : s(z, a) ∉ r.edges := by
    intro he
    dsimp [r] at he
    simp only [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · exact hzq (q.fst_mem_support_of_mem_edges he)
    · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at he
      rcases he with ⟨hzb', haz⟩ | ⟨_, hab'⟩
      · exact hza.ne haz.symm
      · exact hab hab'
  let c : G.Walk z z := r.cons hza
  have hc : c.IsCycle := by
    dsimp [c]
    exact (Walk.cons_isCycle_iff r hza).2 ⟨hr, hclose⟩
  have hsubx : (G.neighborSet x).Subsingleton := by
    obtain ⟨nx, hnx, huniqx⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
    intro u hu v hv
    exact (huniqx u hu).trans (huniqx v hv).symm
  have hsuby : (G.neighborSet y).Subsingleton := by
    obtain ⟨ny, hny, huniqy⟩ := degree_eq_one_iff_existsUnique_adj.mp hy
    intro u hu v hv
    exact (huniqy u hu).trans (huniqy v hv).symm
  have hxz : x ≠ z := fun hxz => hz (hxz ▸ hxs)
  have hyz : y ≠ z := fun hyz => hz (hyz ▸ hys)
  have hxnot : x ∉ c.support :=
    hc.isTrail.not_mem_support_of_subsingleton_neighborSet hxz hxz hsubx
  have hynot : y ∉ c.support :=
    hc.isTrail.not_mem_support_of_subsingleton_neighborSet hyz hyz hsuby
  have hqC : ∀ ⦃w : α⦄, w ∈ q.support → w ∈ c.support := by
    intro w hw
    have hwr : w ∈ r.support := by
      dsimp [r]
      exact q.support_subset_support_concat hzb.symm hw
    dsimp [c]
    exact r.support_subset_support_cons hza hwr
  have hqsub : q.support.toFinset ⊆ (s.erase x).erase y := by
    intro w hw
    have hwq : w ∈ q.support := by simpa using hw
    have hws : w ∈ s := hq_s w hwq
    have hwx : w ≠ x := by
      intro hwx
      subst w
      exact hxnot (hqC hwq)
    have hwy : w ≠ y := by
      intro hwy
      subst w
      exact hynot (hqC hwq)
    simp [hws, hwx, hwy]
  have hqcard : q.support.toFinset.card = q.length + 1 := by
    rw [List.toFinset_card_of_nodup hq.support_nodup, q.length_support]
  have hy_erase : y ∈ s.erase x := by simp [hys, hxy.symm]
  have hcard := Finset.card_le_card hqsub
  rw [hqcard, Finset.card_erase_of_mem hy_erase,
    Finset.card_erase_of_mem hxs] at hcard
  have hclen : c.length = q.length + 2 := by simp [c, r]
  have hg := G.girth_le_length hc
  omega
end IsTree
end SimpleGraph
