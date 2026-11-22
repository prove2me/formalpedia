-- Prove2me | solution 1 for Paper.Hypergraph.glue_component_decompositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:30.939698+00:00
-- url     : https://prove2.me/submissions/f02ede52-5a32-4b8e-aedb-8877e50f5639

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_forest_acyclic
import Theorems.Thm_Paper_Hypergraph_exists_component_of_mem
import Theorems.Thm_Paper_Hypergraph_finite_tree_decomposition
import Theorems.Thm_Paper_Hypergraph_component_eq_of_mem
import Theorems.Thm_Paper_Hypergraph_edge_subset_component

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (b : Finset ℕ → ℝ) (r : ℝ)
    (hzero : b ∅ ≤ r)
    (hcomp : ∀ C ∈ H.components, ∃ n, ∃ D : (H.induce C).TreeDecomposition n,
      ∀ t, b (D.bag t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∀ t, b (D.bag t) ≤ r := by
  classical
  by_cases hV : H.vertices.Nonempty
  swap
  · have he : H.vertices = ∅ := not_nonempty_iff_eq_empty.mp hV
    exact ⟨0, H.oneBag, fun t => by simpa [oneBag, he] using hzero⟩
  let I := {C // C ∈ H.components}
  obtain ⟨v, hv⟩ := hV
  obtain ⟨C, hC, _⟩ := H.exists_component_of_mem hv
  letI : Nonempty I := ⟨⟨C, hC⟩⟩
  choose n D hD using (fun i : I => hcomp i i.property)
  let T := Σ i : I, Fin (n i + 1)
  letI : Nonempty T := ⟨⟨⟨C, hC⟩, 0⟩⟩
  let G : SimpleGraph T := forestGraph (fun i => (D i).tree)
  obtain ⟨F, hGF, _, hF⟩ := (SimpleGraph.connected_top (V := T)).exists_isTree_le_of_le_of_isAcyclic
    (H := G) le_top (forest_acyclic _ (fun i => (D i).isTree.isAcyclic))
  let bag : T → Finset ℕ := fun t => (D t.1).bag t.2
  have hsub (t : T) : bag t ⊆ H.vertices :=
    fun v hv => (mem_inter.mp ((D t.1).bag_subset t.2 hv)).1
  apply H.finite_tree_decomposition F hF bag hsub _ _ _ b r (fun t => hD t.1 t.2)
  · intro e he
    obtain ⟨v, hve⟩ := H.edge_nonempty e he
    obtain ⟨C, hC, hvC⟩ := H.exists_component_of_mem (H.edge_subset e he hve)
    let i : I := ⟨C, hC⟩
    have heC : H.edge e ⊆ C := H.edge_subset_component hC he hve hvC
    have heJ : e ∈ (H.induce C).edges := mem_filter.mpr ⟨he, ⟨v, mem_inter.mpr ⟨hve, hvC⟩⟩⟩
    obtain ⟨t, ht⟩ := (D i).edge_covered e heJ
    refine ⟨⟨i, t⟩, ?_⟩
    intro v hv
    exact ht (mem_inter.mpr ⟨hv, heC hv⟩)
  · intro v hv
    obtain ⟨C, hC, hvC⟩ := H.exists_component_of_mem hv
    let i : I := ⟨C, hC⟩
    obtain ⟨t, ht⟩ := (D i).vertex_covered v (mem_inter.mpr ⟨hv, hvC⟩)
    exact ⟨⟨i, t⟩, ht⟩
  · intro v hv a c
    rcases a with ⟨⟨i, a⟩, ha⟩
    rcases c with ⟨⟨j, c⟩, hc⟩
    have hvi : v ∈ i.val := (mem_inter.mp ((D i).bag_subset a ha)).2
    have hvj : v ∈ j.val := (mem_inter.mp ((D j).bag_subset c hc)).2
    have hij : i = j := Subtype.ext (H.component_eq_of_mem i.property j.property hvi hvj)
    subst j
    let f : (D i).tree.induce {t | v ∈ (D i).bag t} →g F.induce {t | v ∈ bag t} := {
      toFun := fun t => ⟨⟨i, t.val⟩, t.property⟩
      map_rel' := by intro a b hab; exact hGF ⟨rfl, hab⟩ }
    exact ((D i).running_intersection v (mem_inter.mpr ⟨hv, hvi⟩) ⟨a, ha⟩ ⟨c, hc⟩).map f
end Paper.Hypergraph
