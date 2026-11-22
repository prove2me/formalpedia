-- Prove2me | solution 1 for Paper.Hypergraph.recursive_rooted_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:32.165321+00:00
-- url     : https://prove2.me/submissions/a1577118-cfed-4e97-aa2d-e81712b7b2a6

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_exists_component_of_mem
import Theorems.Thm_Paper_Hypergraph_component_eq_of_mem
import Theorems.Thm_Paper_Hypergraph_sep_bounds
import Theorems.Thm_Paper_Hypergraph_recursive_bag_step
import Theorems.Thm_Paper_Hypergraph_child_geometry
import Theorems.Thm_Paper_Hypergraph_child_card_lt
import Theorems.Thm_Paper_Hypergraph_edge_in_child
import Theorems.Thm_Paper_Hypergraph_glue_rooted_bags

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {η r : ℝ}
    (hη : 0 < η ∧ η < 1) (hr : H.sep η < r)
    (W Z : Finset ℕ) (hW : W ⊆ H.vertices) (hZ : Z ⊆ W)
    (hcost : H.setCoverCost Z ≤ (r + 1) / (1 - η)) :
    ∃ n, ∃ D : (H.induce W).TreeDecomposition n, ∃ root, Z ⊆ D.bag root ∧
      ∀ t, H.setCoverCost (D.bag t) ≤ (r + 1) / (1 - η) + r + 1 := by
  classical
  generalize hm : (W \ Z).card = m
  induction m using Nat.strong_induction_on generalizing W Z with
  | h m ih =>
    have hr0 : 0 ≤ r := (H.sep_bounds hη).1.trans hr.le
    by_cases hWZ : W = Z
    · subst Z
      refine ⟨0, (H.induce W).oneBag, 0, ?_, ?_⟩
      · simpa [oneBag, induce, inter_eq_right.mpr hW]
      · intro t
        simpa only [oneBag, induce, inter_eq_right.mpr hW] using
          (hcost.trans (by linarith : (r + 1) / (1 - η) ≤ (r + 1) / (1 - η) + r + 1))
    have hne : (W \ Z).Nonempty := by
      by_contra hn
      exact hWZ (subset_antisymm
        (sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp hn)) hZ)
    obtain ⟨u, hu⟩ := hne
    obtain ⟨B, hZB, hBW, huB, hBcost, hbound⟩ := H.recursive_bag_step hη hr hW hZ hcost hu
    let I := {K // K ∈ (H.induce (W \ B)).components}
    let bd : I → Finset ℕ := fun i => (H.induce W).boundary B i.val
    let child : I → Finset ℕ := fun i => i.val ∪ bd i
    have hgeom (i : I) := H.child_geometry hBW i.property
    have hchild (i : I) : ∃ n, ∃ D : (H.induce (child i)).TreeDecomposition n,
        ∃ root, bd i ⊆ D.bag root ∧
          ∀ t, H.setCoverCost (D.bag t) ≤ (r + 1) / (1 - η) + r + 1 := by
      apply ih ((child i \ bd i).card) ?_ (child i) (bd i)
        ((hgeom i).1.trans hW) subset_union_right (hbound i i.property) rfl
      change ((i.val ∪ (H.induce W).boundary B i.val) \ (H.induce W).boundary B i.val).card < m
      rw [(hgeom i).2.1, ← hm]
      exact H.child_card_lt hZB hu huB i.property
    choose n D root hroot hwidth using hchild
    let ns : Option I → ℕ := fun i => match i with | none => 0 | some i => n i
    let G : ∀ i : Option I, SimpleGraph (Fin (ns i + 1)) := fun i => match i with
      | none => (H.induce W).oneBag.tree
      | some i => (D i).tree
    let bag : ∀ i : Option I, Fin (ns i + 1) → Finset ℕ := fun i => match i with
      | none => fun _ => B
      | some i => (D i).bag
    let roots : ∀ i : Option I, Fin (ns i + 1) := fun i => match i with
      | none => 0
      | some i => root i
    have hsub (i : Option I) (t : Fin (ns i + 1)) : bag i t ⊆ (H.induce W).vertices := by
      cases i with
      | none => exact fun v hv => mem_inter.mpr ⟨hW (hBW hv), hBW hv⟩
      | some i =>
        intro v hv
        exact mem_inter.mpr ⟨(mem_inter.mp ((D i).bag_subset t hv)).1,
          (hgeom i).1 (mem_inter.mp ((D i).bag_subset t hv)).2⟩
    have hbsub (i : I) (t : Fin (n i + 1)) : (D i).bag t ⊆ child i :=
      fun v hv => (mem_inter.mp ((D i).bag_subset t hv)).2
    obtain ⟨k, E, q, hq, hE⟩ := (H.induce W).glue_rooted_bags G
      (by intro i; cases i with
          | none => exact (H.induce W).oneBag.isTree
          | some i => exact (D i).isTree)
      bag roots none hsub (by
        intro e he
        by_cases heB : (H.induce W).edge e ⊆ B
        · exact ⟨none, 0, heB⟩
        · obtain ⟨K, hK, heK⟩ := H.edge_in_child he heB
          let i : I := ⟨K, hK⟩
          obtain ⟨v, hve⟩ := (H.induce W).edge_nonempty e he
          have heC : e ∈ (H.induce (child i)).edges := mem_filter.mpr
            ⟨(mem_filter.mp he).1, v, mem_inter.mpr ⟨(mem_inter.mp hve).1, heK hve⟩⟩
          obtain ⟨t, ht⟩ := (D i).edge_covered e heC
          exact ⟨some i, t, fun v hv => ht (mem_inter.mpr ⟨(mem_inter.mp hv).1, heK hv⟩)⟩) (by
        intro v hv
        by_cases hvB : v ∈ B
        · exact ⟨none, 0, hvB⟩
        · have hvR : v ∈ (H.induce (W \ B)).vertices :=
            mem_inter.mpr ⟨(mem_inter.mp hv).1, mem_sdiff.mpr ⟨(mem_inter.mp hv).2, hvB⟩⟩
          obtain ⟨K, hK, hvK⟩ := (H.induce (W \ B)).exists_component_of_mem hvR
          let i : I := ⟨K,hK⟩
          obtain ⟨t,ht⟩ := (D i).vertex_covered v
            (mem_inter.mpr ⟨(mem_inter.mp hv).1, mem_union_left _ hvK⟩)
          exact ⟨some i,t,ht⟩) (by
        intro i v a c
        cases i with
        | none =>
          have heq : a = c := by
            apply Subtype.ext
            apply Fin.ext
            have ha := a.val.isLt
            have hc := c.val.isLt
            dsimp [ns] at ha hc
            omega
          exact heq ▸ SimpleGraph.Reachable.refl a
        | some i => exact (D i).running_intersection v ((D i).bag_subset a.val a.property) a c) (by
        intro i t v hv
        cases i with
        | none => exact (mem_inter.mp hv).1
        | some i =>
          apply hroot i
          have hh : v ∈ child i ∩ B := mem_inter.mpr ⟨hbsub i t (mem_inter.mp hv).1, (mem_inter.mp hv).2⟩
          rwa [(hgeom i).2.2] at hh) (by
        intro i j hij a c v hv
        cases i with
        | none => exact (mem_inter.mp hv).1
        | some i =>
          cases j with
          | none => exact (mem_inter.mp hv).2
          | some j =>
            by_contra hvB
            have hiC := hbsub i a (mem_inter.mp hv).1
            have hjC := hbsub j c (mem_inter.mp hv).2
            have hiK : v ∈ i.val := (mem_union.mp hiC).resolve_right
              (fun h => hvB ((filter_subset _ _) h))
            have hjK : v ∈ j.val := (mem_union.mp hjC).resolve_right
              (fun h => hvB ((filter_subset _ _) h))
            exact hij (congrArg some (Subtype.ext
              ((H.induce (W \ B)).component_eq_of_mem i.property j.property hiK hjK))))
      H.setCoverCost ((r + 1) / (1 - η) + r + 1) (by
        intro i t
        cases i with
        | none => exact hBcost
        | some i => exact hwidth i t)
    exact ⟨k,E,q,hZB.trans hq,hE⟩
end Paper.Hypergraph
